#pragma once

#include <category/mpt2/node.hpp>
#include <category/mpt2/node_cursor.hpp>
#include <category/mpt2/state_machine.hpp>
#include <category/mpt2/update.hpp>
#include <category/mpt2/util.hpp>
#include <category/storage/db_storage.hpp>

#include <cstdint>

MONAD_MPT2_NAMESPACE_BEGIN

class WriteTransaction;

// auxiliary structure for upsert, at most one thread can modify it at a time,
// but multiple threads can read it
class UpdateAux
{
    friend class WriteTransaction;

    uint32_t initial_insertion_count_on_pool_creation_{0};
    bool enable_dynamic_history_length_{true};
    bool alternate_slow_fast_writer_{false};
    bool can_write_to_fast_{true};

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
    // void release_unreferenced_chunks();

public:
    int64_t curr_upsert_auto_expire_version{0};
    // compact_virtual_chunk_offset_t compact_offset_fast{
    //     MIN_COMPACT_VIRTUAL_OFFSET};
    // compact_virtual_chunk_offset_t compact_offset_slow{
    //     MIN_COMPACT_VIRTUAL_OFFSET};

    // On disk stuff
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

    chunk_offset_t do_upsert(
        chunk_offset_t root_offset, StateMachine &, UpdateList &&,
        uint64_t version, bool compaction, bool can_write_to_fast);

    void finalize_transaction(chunk_offset_t root_offset, uint64_t version);
};

class WriteTransaction
{
    UpdateAux &aux_;

public:
    explicit WriteTransaction(UpdateAux &aux)
        : aux_(aux)
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

    // TODO
    chunk_offset_t copy_trie();

    void finish(chunk_offset_t root_offset, uint64_t version)
    {
        aux_.finalize_transaction(root_offset, version);
    }
};

// batch upsert, updates can be nested, at most one thread can call upsert at a
// time, implementation is not threadsafe and no need to be
chunk_offset_t upsert(
    UpdateAux &, uint64_t version, StateMachine &, chunk_offset_t old_offset,
    UpdateList &&);

// TODO: copy_trie

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
find(UpdateAux const &, NodeCursor, NibblesView key, uint64_t version);

std::pair<compact_virtual_chunk_offset_t, compact_virtual_chunk_offset_t>
calc_min_offsets(
    Node const &node,
    virtual_chunk_offset_t node_virtual_offset = INVALID_VIRTUAL_OFFSET);

MONAD_MPT2_NAMESPACE_END
