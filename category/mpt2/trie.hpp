#pragma once

#include <category/mpt2/node.hpp>
#include <category/mpt2/node_cursor.hpp>
#include <category/mpt2/state_machine.hpp>
#include <category/mpt2/update.hpp>
#include <category/mpt2/util.hpp>
#include <category/storage/db_storage.hpp>

#include <cstdint>

#include <sys/mman.h>

MONAD_MPT2_NAMESPACE_BEGIN

class WriteTransaction;

// auxiliary structure for upsert, WriteTransaction guarantees at most one
// thread modify it at a time, but multiple threads can read
class UpdateAux
{
    friend class WriteTransaction;

    bool enable_dynamic_history_length_{true};
    // bool can_write_to_fast_{true};

    /******** Compaction ********/
    uint32_t chunks_to_remove_before_count_fast_{0};
    uint32_t chunks_to_remove_before_count_slow_{0};
    // speed control var
    compact_virtual_chunk_offset_t last_block_end_offset_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_end_offset_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_disk_growth_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_disk_growth_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    // compaction range
    compact_virtual_chunk_offset_t compact_offset_range_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_range_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};

    MONAD_STORAGE_NAMESPACE::DbStorage &db_storage_;

    std::mutex write_mutex_;

    void clear_root_offsets_up_to_and_including(uint64_t version);
    void erase_versions_up_to_and_including(uint64_t version);
    void release_unreferenced_chunks();
    void free_compacted_chunks();

    void advance_compact_offsets();

    uint32_t num_chunks(
        MONAD_STORAGE_NAMESPACE::DbStorage::chunk_list list) const noexcept;
    double disk_usage() const noexcept;
    double disk_usage(
        MONAD_STORAGE_NAMESPACE::DbStorage::chunk_list list) const noexcept;

    chunk_offset_t do_upsert(
        chunk_offset_t root_offset, StateMachine &, UpdateList &&,
        uint64_t version, bool compaction, bool can_write_to_fast);

    chunk_offset_t copy_trie_to_dest(
        chunk_offset_t src_root, NibblesView src_prefix, uint64_t dest_version,
        NibblesView dest_prefix);

    void finalize_transaction(chunk_offset_t root_offset, uint64_t version);

public:
    // int64_t curr_upsert_auto_expire_version{0};
    compact_virtual_chunk_offset_t compact_offset_fast{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_slow{
        MIN_COMPACT_VIRTUAL_OFFSET};

    chunk_offset_t node_writer_offset_fast{INVALID_OFFSET};
    chunk_offset_t node_writer_offset_slow{INVALID_OFFSET};

    UpdateAux(
        MONAD_STORAGE_NAMESPACE::DbStorage &,
        std::optional<uint64_t> history_len = {});

    // TODO: add db stats

    storage::DbStorage const &db_storage() const noexcept
    {
        return db_storage_;
    }

    bool is_read_only() const noexcept
    {
        return db_storage_.is_read_only() ||
               db_storage_.is_read_only_allow_dirty();
    }

    virtual_chunk_offset_t
    physical_to_virtual(chunk_offset_t offset) const noexcept;

    Node *parse_node(chunk_offset_t offset) const noexcept;

    chunk_offset_t write_node_to_disk(Node const &node, bool to_fast_list);

    bool exists_version(uint64_t version) const noexcept;

    chunk_offset_t get_root_offset_at_version(uint64_t version) const noexcept;

    void set_latest_finalized_version(uint64_t version) noexcept;
    uint64_t get_latest_finalized_version() const noexcept;
    void set_latest_verified_version(uint64_t version) noexcept;
    uint64_t get_latest_verified_version() const noexcept;
    uint64_t db_history_max_version() const noexcept;
    uint64_t db_history_min_valid_version() const noexcept;
    void set_latest_voted(
        uint64_t const version, bytes32_t const &block_id) noexcept;
    uint64_t get_latest_voted_version() const noexcept;
    bytes32_t get_latest_voted_block_id() const noexcept;
    uint64_t version_history_length() const noexcept;
};

class WriteTransaction
{
    friend class UpdateAux;
    UpdateAux &aux_;

    chunk_offset_t fast_offset_start{INVALID_OFFSET};
    chunk_offset_t slow_offset_start{INVALID_OFFSET};

public:
    explicit WriteTransaction(UpdateAux &aux)
        : aux_(aux)
        , fast_offset_start(aux.node_writer_offset_fast)
        , slow_offset_start(aux.node_writer_offset_slow)
    {
        aux_.write_mutex_.lock();
        MONAD_ASSERT(!aux_.is_read_only());
    }

    ~WriteTransaction()
    {
        aux_.write_mutex_.unlock();
    }

    // upsert on top of the given root into a specific version
    chunk_offset_t do_upsert(
        chunk_offset_t const root_offset, StateMachine &sm,
        UpdateList &&updates, uint64_t const version, bool const compaction,
        bool const can_write_to_fast)
    {
        return aux_.do_upsert(
            root_offset,
            sm,
            std::move(updates),
            version,
            compaction,
            can_write_to_fast);
    };

    chunk_offset_t copy_trie(
        chunk_offset_t const src_root, NibblesView const src_prefix,
        uint64_t const dest_version, NibblesView const dest_prefix)
    {
        return aux_.copy_trie_to_dest(
            src_root, src_prefix, dest_version, dest_prefix);
    }

    void finish(chunk_offset_t root_offset, uint64_t version)
    {
        using namespace MONAD_STORAGE_NAMESPACE;

        // msync the changes since offsets_start to disk
        auto const *m = aux_.db_storage_.db_metadata();
        auto sync_ = [&](chunk_offset_t const start, chunk_offset_t const end) {
            if (start != end) {
                auto const *si = m->at(start.id);
                auto const *ei = m->at(end.id);
                MONAD_ASSERT(si->insertion_count() <= ei->insertion_count());
                MONAD_DEBUG_ASSERT(si->in_fast_list == ei->in_fast_list);
                MONAD_DEBUG_ASSERT(si->in_slow_list == ei->in_slow_list);

                for (auto const *ci = si;; ci = ci->next(m)) {
                    auto const idx = ci->index(m);
                    uint32_t offset = 0;
                    if (ci == si) {
                        offset = round_down_align<CPU_PAGE_BITS>(
                            (uint32_t)start.offset);
                    }
                    else if (ci == ei) {
                        offset =
                            round_up_align<CPU_PAGE_BITS>((uint32_t)end.offset);
                    }
                    MONAD_ASSERT_PRINTF(
                        -1 != ::msync(
                                  aux_.db_storage_.get_data({idx, offset}),
                                  DbStorage::chunk_capacity - offset,
                                  MS_SYNC),
                        "msync failed: %s",
                        strerror(errno));
                    if (ci == ei) {
                        break;
                    }
                }
            }
        };
        sync_(fast_offset_start, aux_.node_writer_offset_fast);
        sync_(slow_offset_start, aux_.node_writer_offset_slow);

        aux_.finalize_transaction(root_offset, version);
    }
};

// batch upsert, updates can be nested, at most one thread can call upsert at a
// time, implementation is not threadsafe and no need to be
chunk_offset_t
upsert(UpdateAux &, StateMachine &, chunk_offset_t old_offset, UpdateList &&);

//////////////////////////////////////////////////////////////////////////////
// find

enum class find_result : uint8_t
{
    unknown,
    success,
    version_no_longer_exist,
    root_node_is_null_failure,
    key_mismatch_failure,
    branch_not_exist_failure,
    key_ends_earlier_than_node_failure,
    need_to_continue_in_io_thread
};
template <class T>
using find_result_type = std::pair<T, find_result>;

using find_cursor_result_type = find_result_type<NodeCursor>;

find_cursor_result_type
find(UpdateAux const &, NodeCursor, NibblesView key, uint64_t version = 0);

std::pair<compact_virtual_chunk_offset_t, compact_virtual_chunk_offset_t>
calc_min_offsets(
    Node const &node,
    virtual_chunk_offset_t node_virtual_offset = INVALID_VIRTUAL_OFFSET);

MONAD_MPT2_NAMESPACE_END
