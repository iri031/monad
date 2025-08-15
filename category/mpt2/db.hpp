#pragma once
#include <memory>

#include <category/core/bytes.hpp>
#include <category/core/lru/static_lru_cache.hpp>
#include <category/core/result.hpp>
#include <category/mpt2/config.hpp>
#include <category/mpt2/nibbles_view.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/node_cursor.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/update.hpp>
#include <category/storage/db_storage.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

struct OnDiskDbConfig;
struct StateMachine;

struct TraverseMachine;

// Simply RWDb impl, TODO: change to add rodb
class Db
{
    StateMachine &sm_;
    MONAD_STORAGE_NAMESPACE::DbStorage storage_;
    UpdateAux aux_;

    std::unique_ptr<WriteTransaction> wt_;
    chunk_offset_t root_offset_{INVALID_OFFSET};
    uint64_t version_{INVALID_BLOCK_NUM};

public:
    Db(StateMachine &, OnDiskDbConfig const &);

    Db(Db const &) = delete;
    Db(Db &&) = delete;
    Db &operator=(Db const &) = delete;
    Db &operator=(Db &&) = delete;
    ~Db() = default;

    // The find, get, and get_data API calls return non-owning references.
    // The result lifetime ends when a subsequent operation reloads the trie
    // root. This can happen due to an RWDb upsert, an RODb reading a different
    // version, or an RODb reading the same version that has been updated by an
    // RWDb in another process.
    // The `block_id` parameter specify the version to read from, and is also
    // used for version control validation. These calls may wait on a fiber
    // future.
    Result<NodeCursor> find(NodeCursor, NibblesView, uint64_t block_id) const;
    Result<NodeCursor> find(NibblesView prefix, uint64_t block_id) const;
    Result<byte_string_view> get(NibblesView, uint64_t block_id) const;
    Result<byte_string_view> get_data(NibblesView, uint64_t block_id) const;
    Result<byte_string_view>
    get_data(NodeCursor, NibblesView, uint64_t block_id) const;

    NodeCursor load_root_for_version(uint64_t block_id) const;

    void start_transaction(uint64_t block_id)
    {
        wt_ = std::make_unique<WriteTransaction>(aux_);
        root_offset_ = aux_.get_root_offset_at_version(block_id);
        version_ = block_id;
    }

    void finish_transaction(uint64_t block_id)
    {
        wt_->finish(root_offset_, block_id);

        wt_.reset();
        root_offset_ = INVALID_OFFSET;
        version_ = INVALID_BLOCK_NUM;
    }

    void copy_trie(
        uint64_t src_version, NibblesView src, uint64_t dest_version,
        NibblesView dest);

    void upsert(
        UpdateList, uint64_t block_id, bool enable_compaction = true,
        bool can_write_to_fast = true);

    void upsert_transaction(
        uint64_t start_version, UpdateList, uint64_t end_version,
        bool enable_compaction = true, bool can_write_to_fast = true);

    void update_finalized_version(uint64_t version);
    void update_verified_version(uint64_t version);
    void update_voted_metadata(uint64_t version, bytes32_t const &block_id);
    uint64_t get_latest_finalized_version() const;
    uint64_t get_latest_verified_version() const;
    bytes32_t get_latest_voted_block_id() const;
    uint64_t get_latest_voted_version() const;

    // Traverse APIs: return value indicates if we have finished the full
    // traversal or not.
    // Parallel traversal is a single threaded out of order traverse using async
    // i/o. Note that RWDb impl waits on a fiber future, therefore any parallel
    // traverse run on RWDb should not do any blocking i/o because that will
    // block the fiber and hang. If you have to do blocking i/o during the
    // traversal on RWDb, use the `traverse_blocking` api below.
    // bool traverse(
    //     NodeCursor, TraverseMachine &, uint64_t block_id,
    //     size_t concurrency_limit = 4096);

    bool traverse(NodeCursor root, TraverseMachine &machine, uint64_t version);

    uint64_t get_latest_version() const;
    uint64_t get_earliest_version() const;
    uint64_t get_history_length() const;

    // This function moves trie from source to destination version in db
    // history. Only the RWDb can call this API for state sync purposes.
    void move_trie_version_forward(uint64_t, uint64_t)
    {
        // TODO:
    }

    bool is_read_only() const;

    bool is_on_disk() const noexcept
    {
        return true;
    }
};

MONAD_MPT2_NAMESPACE_END
