#pragma once

#include <monad/async/concepts.hpp>
#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/result.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

MONAD_MPT_NAMESPACE_BEGIN

struct OnDiskDbConfig;
struct ReadOnlyOnDiskDbConfig;
struct StateMachine;
struct TraverseMachine;

namespace detail
{
    template <class T>
    struct DbGetSender;
}

class Db
{
    template <class T>
    friend struct detail::DbGetSender;

private:
    struct Impl;
    struct RWOnDisk;
    struct ROOnDisk;
    struct InMemory;

    std::unique_ptr<Impl> impl_;

public:
    Db(StateMachine &); // In-memory mode
    Db(StateMachine &, OnDiskDbConfig const &);
    Db(ReadOnlyOnDiskDbConfig const &);

    Db(Db const &) = delete;
    Db(Db &&) = delete;
    Db &operator=(Db const &) = delete;
    Db &operator=(Db &&) = delete;
    ~Db();

    // May wait on a fiber future
    Result<NodeCursor>
    find(NodeCursor, NibblesView, uint64_t block_id = 0) const;
    // Search path includes block id in the prefix
    Result<NodeCursor> find(NibblesView prefix, uint64_t block_id = 0) const;
    // Search path includes block id in the prefix
    Result<byte_string_view> get(NibblesView, uint64_t block_id = 0) const;
    // Search path includes block id in the prefix
    Result<byte_string_view> get_data(NibblesView, uint64_t block_id = 0) const;
    Result<byte_string_view>
    get_data(NodeCursor, NibblesView, uint64_t block_id = 0) const;

    void upsert(
        UpdateList, uint64_t block_id = 0, bool enable_compaction = true,
        bool can_write_to_fast = true);
    // Traverse APIs: return value indicates if we have finished the full
    // traversal or not.
    // Parallel traversal is a single threaded out of order traverse using async
    // i/o. Note that RWDb impl waits on a fiber future, therefore any parallel
    // traverse run on RWDb should not do any blocking i/o because that will
    // block the fiber and hang. If you have to do blocking i/o during the
    // traversal on RWDb, use the `traverse_blocking` api below.
    // TODO: fix the excessive memory issue by pausing traverse when there are N
    // outstanding requests
    bool traverse(NodeCursor, TraverseMachine &, uint64_t block_id = 0);
    // Blocking traverse never wait on a fiber future.
    bool
    traverse_blocking(NodeCursor, TraverseMachine &, uint64_t block_id = 0);
    NodeCursor root() const noexcept;
    std::optional<uint64_t> get_latest_block_id() const;
    std::optional<uint64_t> get_earliest_block_id() const;
    // This function moves a source trie to under a destination version,
    // assuming the source trie is the only version present.
    // Only the RWDb can call this API for state sync purposes.
    void move_subtrie(uint64_t src, uint64_t dest);

    // Always true if not RO. True if this DB is the latest DB (fast)
    bool is_latest() const;
    // Load the latest DB root
    void load_latest();
    // Load the tree of nodes in the current DB root as far as the caching
    // policy allows. RW only.
    size_t prefetch();
    // Pump any async DB operations. RO only.
    size_t poll(bool blocking, size_t count = 1);
};

template <class T>
struct detail::DbGetSender
{
    using result_type = async::result<T>;

public:
    Db &db;

    enum op_t : uint8_t
    {
        op_get1,
        op_get_data1,
        op_get2,
        op_get_data2
    } op_type;

    NodeCursor cur;
    Nibbles const nv;
    uint64_t const block_id{0};

    find_result_type res_;

public:
    constexpr DbGetSender(
        Db &db_, op_t const op_type_, NibblesView const n,
        uint64_t const block_id_ = 0)
        : db(db_)
        , op_type(op_type_)
        , nv(n)
        , block_id(block_id_)
    {
    }

    constexpr DbGetSender(
        Db &db_, op_t const op_type_, NodeCursor const cur_,
        NibblesView const n)
        : db(db_)
        , op_type(op_type_)
        , cur(cur_)
        , nv(n)
    {
    }

    DbGetSender(DbGetSender &&o) noexcept
        : db(o.db)
        , op_type(o.op_type)
        , cur(o.cur)
        , nv(const_cast<Nibbles &&>(std::move(o.nv)))
        , block_id(o.block_id)
        , res_(std::move(o.res_))
    {
    }

    async::result<void>
    operator()(async::erased_connected_operation *io_state) noexcept;

    result_type completed(
        async::erased_connected_operation *, async::result<void> res) noexcept;
};

inline constexpr detail::DbGetSender<byte_string>
make_get_sender(Db &db, NibblesView const nv, uint64_t const block_id = 0)
{
    return {db, detail::DbGetSender<byte_string>::op_t::op_get1, nv, block_id};
}

inline constexpr detail::DbGetSender<byte_string>
make_get_data_sender(Db &db, NibblesView const nv, uint64_t const block_id = 0)
{
    return {
        db, detail::DbGetSender<byte_string>::op_t::op_get_data1, nv, block_id};
}

inline constexpr detail::DbGetSender<NodeCursor>
make_get_sender(Db &db, NodeCursor const cur, NibblesView const nv)
{
    return {db, detail::DbGetSender<NodeCursor>::op_t::op_get2, cur, nv};
}

inline constexpr detail::DbGetSender<byte_string>
make_get_data_sender(Db &db, NodeCursor const cur, NibblesView const nv)
{
    return {db, detail::DbGetSender<byte_string>::op_t::op_get_data2, cur, nv};
}

MONAD_MPT_NAMESPACE_END
