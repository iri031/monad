#include <category/mpt2/db.hpp>

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/connected_operation.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/async/sender_errc.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/result.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/boost_fiber_workarounds.hpp>
#include <category/mpt/find_request_sender.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt2/db_error.hpp>
#include <category/mpt2/nibbles_view.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/ondisk_db_config.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/update.hpp>
#include <category/mpt2/util.hpp>

#include <boost/container/deque.hpp>
#include <boost/fiber/operations.hpp>

#include <quill/Quill.h>

#include <atomic>
#include <cerrno>
#include <chrono>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <iterator>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <system_error>
#include <thread>
#include <utility>
#include <variant>
#include <vector>

#include <fcntl.h>
#include <linux/fs.h>
#include <unistd.h>

#undef BLOCK_SIZE // without this concurrentqueue.h gets sad
#include <concurrentqueue.h>

MONAD_MPT2_NAMESPACE_BEGIN

namespace detail
{
    struct void_receiver
    {
        void set_value(
            async::erased_connected_operation *, async::result<void>) const
        {
        }
    };
}

struct Db::Impl
{
    virtual ~Impl() = default;

    virtual Node *root() = 0;
    virtual UpdateAux &aux() = 0;
    virtual void upsert_fiber_blocking(
        UpdateList &&, uint64_t, bool enable_compaction, bool can_write_to_fast,
        bool write_root) = 0;
    virtual void copy_trie_fiber_blocking(
        uint64_t src_version, NibblesView src, uint64_t dest_version,
        NibblesView dest, bool blocked_by_write = true) = 0;
    virtual find_cursor_result_type find_fiber_blocking(
        NodeCursor const &root, NibblesView const &key, uint64_t version) = 0;
    virtual size_t prefetch_fiber_blocking() = 0;
    virtual NodeCursor load_root_for_version(uint64_t version) = 0;

    virtual bool traverse_fiber_blocking(
        Node &, TraverseMachine &, uint64_t version,
        size_t concurrency_limit) = 0;

    virtual void
    move_trie_version_fiber_blocking(uint64_t src, uint64_t dest) = 0;
    virtual void update_finalized_version(uint64_t) = 0;
    virtual void update_verified_version(uint64_t) = 0;
    virtual uint64_t get_latest_finalized_version() const = 0;
    virtual uint64_t get_latest_verified_version() const = 0;
};

AsyncIOContext::AsyncIOContext(ReadOnlyOnDiskDbConfig const &options)
    : pool{[&] -> async::storage_pool {
        async::storage_pool::creation_flags pool_options;
        pool_options.open_read_only = true;
        pool_options.disable_mismatching_storage_pool_check =
            options.disable_mismatching_storage_pool_check;
        MONAD_ASSERT(!options.dbname_paths.empty());
        return async::storage_pool{
            options.dbname_paths,
            async::storage_pool::mode::open_existing,
            pool_options};
    }()}
    , read_ring{monad::io::RingConfig{
          options.uring_entries, false, options.sq_thread_cpu}}
    , buffers{io::make_buffers_for_read_only(
          read_ring, options.rd_buffers,
          async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE)}
    , io{pool, buffers}
{
    io.set_capture_io_latencies(options.capture_io_latencies);
    io.set_concurrent_read_io_limit(options.concurrent_read_io_limit);
    io.set_eager_completions(options.eager_completions);
}

AsyncIOContext::AsyncIOContext(OnDiskDbConfig const &options)
    : pool{[&] -> async::storage_pool {
        auto len = options.file_size_db * 1024 * 1024 * 1024 + 24576;
        if (options.dbname_paths.empty()) {
            return async::storage_pool{
                async::use_anonymous_sized_inode_tag{}, len};
        }
        // initialize db file on disk
        for (auto const &dbname_path : options.dbname_paths) {
            if (!std::filesystem::exists(dbname_path)) {
                int const fd = ::open(
                    dbname_path.c_str(), O_CREAT | O_RDWR | O_CLOEXEC, 0600);
                if (-1 == fd) {
                    throw std::system_error(errno, std::system_category());
                }
                auto unfd =
                    monad::make_scope_exit([fd]() noexcept { ::close(fd); });
                if (-1 == ::ftruncate(fd, len)) {
                    throw std::system_error(errno, std::system_category());
                }
            }
        }
        return async::storage_pool{
            options.dbname_paths,
            options.append ? async::storage_pool::mode::open_existing
                           : async::storage_pool::mode::truncate};
    }()}
    , read_ring{{options.uring_entries, options.enable_io_polling, options.sq_thread_cpu}}
    , write_ring{options.wr_buffers}
    , buffers{io::make_buffers_for_segregated_read_write(
          read_ring, *write_ring, options.rd_buffers, options.wr_buffers,
          async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
          async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)}
    , io{pool, buffers}
{
    io.set_capture_io_latencies(options.capture_io_latencies);
    io.set_concurrent_read_io_limit(options.concurrent_read_io_limit);
    io.set_eager_completions(options.eager_completions);
}

class Db::ROOnDiskBlocking final : public Db::Impl
{
    storage::DbStorage db_storage_;
    UpdateAux aux_;
    chunk_offset_t last_loaded_root_offset_;
    Node *root_;

public:
    explicit ROOnDiskBlocking(ReadOnlyOnDiskDbConfig const &options)
        : db_storage_{options.dbname_paths[0], monad::storage::DbStorage::Mode::open_existing}
        , aux_(db_storage_, std::nullopt)
        , last_loaded_root_offset_{db_storage_.get_root_offset_at_version(
              db_storage_.db_history_max_version())}
    {
    }

#if 0
    explicit ROOnDiskBlocking(storage::DbStorage &storage)
        : aux_(storage, std::nullopt)
        , last_loaded_root_offset_{storage.get_root_offset_at_version(
              storage.db_history_max_version())}
        , root_{
              last_loaded_root_offset_ == INVALID_OFFSET
                  ? nullptr
                  : aux_.parse_node(last_loaded_root_offset_)}
    {
    }
#endif

    virtual ~ROOnDiskBlocking() {}

    virtual Node *root() override
    {
        return root_;
    }

    virtual UpdateAux &aux() override
    {
        return aux_;
    }

    virtual void
    upsert_fiber_blocking(UpdateList &&, uint64_t, bool, bool, bool) override
    {
        MONAD_ABORT()
    }

    virtual find_cursor_result_type find_fiber_blocking(
        NodeCursor const &root, NibblesView const &key,
        uint64_t const version) override
    {
        if (!root.is_valid()) {
            return {NodeCursor{}, find_result::root_node_is_null_failure};
        }
        // the root we last loaded does not contain the version we want to find
        if (!aux().exists_version(version)) {
            return {NodeCursor{}, find_result::version_no_longer_exist};
        }
        auto const res = mpt2::find(aux(), root, key, version);
        // verify version still valid in history after success
        return aux().exists_version(version)
                   ? res
                   : find_cursor_result_type{
                         NodeCursor{}, find_result::version_no_longer_exist};
    }

    virtual void move_trie_version_fiber_blocking(uint64_t, uint64_t) override
    {
        MONAD_ABORT()
    }

    virtual size_t prefetch_fiber_blocking() override
    {
        MONAD_ABORT()
    }

    virtual void copy_trie_fiber_blocking(
        uint64_t, NibblesView, uint64_t, NibblesView, bool) override
    {
        MONAD_ABORT()
    }

    virtual bool traverse_fiber_blocking(
        Node & /*node*/, TraverseMachine & /*machine*/,
        uint64_t const /*version*/, size_t const /*concurrency_limit*/) override
    {
        // TODO
        return false;
    }

    virtual NodeCursor load_root_for_version(uint64_t const version) override
    {
        auto const root_offset = aux().get_root_offset_at_version(version);
        if (root_offset == INVALID_OFFSET) {
            root_ = nullptr;
            last_loaded_root_offset_ = root_offset;
            return NodeCursor{};
        }
        if (last_loaded_root_offset_ != root_offset) {
            last_loaded_root_offset_ = root_offset;
            root_ = aux().parse_node(root_offset);
        }
        return root_ ? NodeCursor{*root_} : NodeCursor{};
    }

    virtual void update_finalized_version(uint64_t) override
    {
        MONAD_ABORT()
    }

    virtual void update_verified_version(uint64_t) override
    {
        MONAD_ABORT()
    }

    virtual uint64_t get_latest_finalized_version() const override
    {
        return aux_.get_latest_finalized_version();
    }

    virtual uint64_t get_latest_verified_version() const override
    {
        return aux_.get_latest_verified_version();
    }
};

#if 0
// TODO
class Db::InMemory final : public Db::Impl
{
    UpdateAux aux_;
    StateMachine &machine_;
    Node::UniquePtr root_;

public:
    explicit InMemory(StateMachine &machine)
        : aux_{nullptr}
        , machine_{machine}
    {
    }

    virtual Node::UniquePtr &root() override
    {
        return root_;
    }

    virtual UpdateAux<> &aux() override
    {
        return aux_;
    }

    virtual void upsert_fiber_blocking(
        UpdateList &&list, uint64_t const version, bool, bool, bool) override
    {
        root_ = aux_.do_update(
            std::move(root_), machine_, std::move(list), version, false);
    }

    virtual void copy_trie_fiber_blocking(
        uint64_t, NibblesView, uint64_t, NibblesView, bool) override
    {
    }

    virtual find_cursor_result_type find_fiber_blocking(
        NodeCursor const &root, NibblesView const &key,
        uint64_t const version = 0) override
    {
        return find_blocking(aux(), root, key, version);
    }

    virtual size_t prefetch_fiber_blocking() override
    {
        return 0;
    }

    virtual size_t poll(bool, size_t) override
    {
        return 0;
    }

    virtual bool traverse_fiber_blocking(
        Node &node, TraverseMachine &machine, uint64_t const block_id,
        size_t) override
    {
        return preorder_traverse_blocking(aux_, node, machine, block_id);
    }

    virtual void move_trie_version_fiber_blocking(uint64_t, uint64_t) override
    {
        MONAD_ABORT()
    }

    virtual NodeCursor load_root_for_version(uint64_t) override
    {
        return root() ? NodeCursor{*root()} : NodeCursor{};
    }

    virtual void update_verified_version(uint64_t) override {}

    virtual void update_finalized_version(uint64_t) override {}

    virtual uint64_t get_latest_finalized_version() const override
    {
        return INVALID_BLOCK_NUM;
    }

    virtual uint64_t get_latest_verified_version() const override
    {
        return INVALID_BLOCK_NUM;
    }
};

struct OnDiskWithWorkerThreadImpl
{
    struct FiberUpsertRequest
    {
        threadsafe_boost_fibers_promise<Node::UniquePtr> *promise;
        Node::UniquePtr prev_root;
        std::reference_wrapper<StateMachine> sm;
        UpdateList updates;
        uint64_t version;
        bool enable_compaction;
        bool can_write_to_fast;
        bool write_root;
    };

    struct FiberCopyTrieRequest
    {
        threadsafe_boost_fibers_promise<Node::UniquePtr> *promise;
        std::reference_wrapper<Node> src_root;
        NibblesView src;
        uint64_t src_version;
        Node::UniquePtr dest_root;
        NibblesView dest;
        uint64_t dest_version;
        bool blocked_by_write;
    };

    struct FiberLoadAllFromBlockRequest
    {
        threadsafe_boost_fibers_promise<size_t> *promise;
        NodeCursor root;
        std::reference_wrapper<StateMachine> sm;
    };

    struct FiberTraverseRequest
    {
        threadsafe_boost_fibers_promise<bool> *promise;
        std::reference_wrapper<Node> root;
        std::reference_wrapper<TraverseMachine> machine;
        uint64_t version;
        size_t concurrency_limit;
    };

    struct MoveSubtrieRequest
    {
        threadsafe_boost_fibers_promise<void> *promise;
        uint64_t src;
        uint64_t dest;
    };

    struct FiberLoadRootVersionRequest
    {
        threadsafe_boost_fibers_promise<Node::UniquePtr> *promise;
        uint64_t version;
    };

    struct RODbFiberFindOwningNodeRequest
    {
        threadsafe_boost_fibers_promise<find_result_type<OwningNodeCursor>>
            *promise;
        OwningNodeCursor start;
        NibblesView key;
        uint64_t version;
    };

    using Comms = std::variant<
        std::monostate, FiberLoadAllFromBlockRequest, FiberTraverseRequest,
        MoveSubtrieRequest, FiberLoadRootVersionRequest, FiberCopyTrieRequest,
        RODbFiberFindOwningNodeRequest>;

    ::moodycamel::ConcurrentQueue<Comms> comms_;
    std::mutex lock_;
    std::condition_variable cond_;

    struct DbAsyncWorker
    {
        OnDiskWithWorkerThreadImpl *parent;
        AsyncIOContext async_io;
        UpdateAux aux;
        std::atomic<bool> sleeping{false}, done{false};

        DbAsyncWorker(
            OnDiskWithWorkerThreadImpl *const parent,
            ReadOnlyOnDiskDbConfig const &options)
            : parent(parent)
            , async_io(options)
            , aux(&async_io.io)
        {
        }

        DbAsyncWorker(
            OnDiskWithWorkerThreadImpl *const parent,
            OnDiskDbConfig const &options)
            : parent(parent)
            , async_io(options)
            , aux{&async_io.io, options.fixed_history_length}
        {
            if (options.rewind_to_latest_finalized) {
                auto const latest_block_id = aux.get_latest_finalized_version();
                if (latest_block_id == INVALID_BLOCK_NUM) {
                    aux.clear_ondisk_db();
                }
                else {
                    aux.rewind_to_version(latest_block_id);
                }
            }
        }

        void rodb_run(size_t const node_lru_size)
        {
            inflight_map_owning_t inflight;
            NodeCache node_cache{
                node_lru_size,
                virtual_chunk_offset_t::invalid_value(),
                nullptr};

            ::boost::container::deque<
                threadsafe_boost_fibers_promise<find_owning_cursor_result_type>>
                find_owning_cursor_promises;

            Comms request;
            unsigned did_nothing_count = 0;
            while (!done.load(std::memory_order_acquire)) {
                bool did_nothing = true;
                if (parent->comms_.try_dequeue(request)) {
                    if (auto *req = std::get_if<8>(&request); req != nullptr) {
                        find_owning_cursor_promises.emplace_back(
                            std::move(*req->promise));
                        req->promise = &find_owning_cursor_promises.back();
                        if (req->start.is_valid()) {
                            find_owning_notify_fiber_future(
                                aux,
                                node_cache,
                                inflight,
                                *req->promise,
                                req->start,
                                req->key,
                                req->version);
                        }
                        else {
                            MONAD_ASSERT(req->key.empty());
                            load_root_notify_fiber_future(
                                aux,
                                node_cache,
                                inflight,
                                *req->promise,
                                req->version);
                        }
                    }
                    did_nothing = false;
                }
                async_io.io.poll_nonblocking(1);
                boost::this_fiber::yield();
                if (boost::fibers::has_ready_fibers()) {
                    did_nothing = false;
                }
                if (did_nothing && async_io.io.io_in_flight() > 0) {
                    did_nothing = false;
                }
                while (!find_owning_cursor_promises.empty() &&
                       find_owning_cursor_promises.front()
                           .future_has_been_destroyed()) {
                    find_owning_cursor_promises.pop_front();
                }
                if (!find_owning_cursor_promises.empty()) {
                    did_nothing = false;
                }
                if (did_nothing) {
                    did_nothing_count++;
                }
                else {
                    did_nothing_count = 0;
                }
                if (did_nothing_count > 1000000) {
                    std::unique_lock g(parent->lock_);
                    sleeping.store(true, std::memory_order_release);
                    /* Very irritatingly, Boost.Fiber may have fibers scheduled
                     which weren't ready before, and if we sleep forever here
                     then they never run and cause anything waiting on them to
                     hang. So pulse Boost.Fiber every second at most for those
                     extremely rare occasions.
                     */
                    parent->cond_.wait_for(g, std::chrono::seconds(1), [this] {
                        return done.load(std::memory_order_acquire) ||
                               parent->comms_.size_approx() > 0;
                    });
                    sleeping.store(false, std::memory_order_release);
                }
            }
        }

        // Runs in the triedb worker thread
        void rwdb_run()
        {
            inflight_map_t inflights;
            ::boost::container::deque<
                threadsafe_boost_fibers_promise<find_cursor_result_type>>
                find_promises;
            ::boost::container::deque<
                threadsafe_boost_fibers_promise<Node::UniquePtr>>
                upsert_promises;
            ::boost::container::deque<threadsafe_boost_fibers_promise<size_t>>
                prefetch_promises;
            ::boost::container::deque<threadsafe_boost_fibers_promise<bool>>
                traverse_promises;
            ::boost::container::deque<threadsafe_boost_fibers_promise<void>>
                move_trie_version_promises;

            Comms request;
            unsigned did_nothing_count = 0;
            while (!done.load(std::memory_order_acquire)) {
                bool did_nothing = true;
                if (parent->comms_.try_dequeue(request)) {
                    if (auto *req = std::get_if<1>(&request); req != nullptr) {
                        // The promise needs to hang around until its future is
                        // destructed, otherwise there is a race within
                        // Boost.Fiber. So we move the promise out of the
                        // submitting thread into a local deque which gets
                        // emptied when its future gets destroyed.
                        find_promises.emplace_back(std::move(*req->promise));
                        req->promise = &find_promises.back();
                        find_notify_fiber_future(
                            aux,
                            inflights,
                            *req->promise,
                            req->start,
                            req->key);
                    }
                    else if (auto *req = std::get_if<2>(&request);
                             req != nullptr) {
                        // Ditto to above
                        upsert_promises.emplace_back(std::move(*req->promise));
                        req->promise = &upsert_promises.back();
                        req->promise->set_value(aux.do_update(
                            std::move(req->prev_root),
                            req->sm,
                            std::move(req->updates),
                            req->version,
                            req->enable_compaction,
                            req->can_write_to_fast,
                            req->write_root));
                    }
                    else if (auto *req = std::get_if<3>(&request);
                             req != nullptr) {
                        // Ditto to above
                        prefetch_promises.emplace_back(
                            std::move(*req->promise));
                        req->promise = &prefetch_promises.back();
                        req->promise->set_value(
                            mpt::load_all(aux, req->sm, req->root));
                    }
                    else if (auto *req = std::get_if<4>(&request);
                             req != nullptr) {
                        // Ditto to above
                        traverse_promises.emplace_back(
                            std::move(*req->promise));
                        req->promise = &traverse_promises.back();
                        // verify version is valid
                        if (aux.version_is_valid_ondisk(req->version)) {
                            req->promise->set_value(preorder_traverse_ondisk(
                                aux,
                                req->root,
                                req->machine,
                                req->version,
                                req->concurrency_limit));
                        }
                        else {
                            req->promise->set_value(false);
                        }
                    }
                    else if (auto *req = std::get_if<5>(&request);
                             req != nullptr) {
                        // Ditto to above
                        move_trie_version_promises.emplace_back(
                            std::move(*req->promise));
                        req->promise = &move_trie_version_promises.back();
                        aux.move_trie_version_forward(req->src, req->dest);
                        req->promise->set_value();
                    }
                    else if (auto *req = std::get_if<6>(&request);
                             req != nullptr) {
                        // share the same promise type as upsert
                        upsert_promises.emplace_back(std::move(*req->promise));
                        req->promise = &upsert_promises.back();
                        auto const root_offset =
                            aux.get_root_offset_at_version(req->version);
                        MONAD_ASSERT(root_offset != INVALID_OFFSET);
                        req->promise->set_value(
                            read_node_blocking(aux, root_offset, req->version));
                    }
                    else if (auto *req = std::get_if<7>(&request);
                             req != nullptr) {
                        // share the same promise type as upsert
                        upsert_promises.emplace_back(std::move(*req->promise));
                        req->promise = &upsert_promises.back();
                        auto root = copy_trie_to_dest(
                            aux,
                            req->src_root,
                            req->src,
                            req->src_version,
                            std::move(req->dest_root),
                            req->dest,
                            req->dest_version,
                            req->blocked_by_write);
                        req->promise->set_value(std::move(root));
                    }
                    did_nothing = false;
                }
                async_io.io.poll_nonblocking(1);
                boost::this_fiber::yield();
                if (boost::fibers::has_ready_fibers()) {
                    did_nothing = false;
                }
                if (did_nothing && async_io.io.io_in_flight() > 0) {
                    did_nothing = false;
                }
                while (!find_promises.empty() &&
                       find_promises.front().future_has_been_destroyed()) {
                    find_promises.pop_front();
                }
                while (!upsert_promises.empty() &&
                       upsert_promises.front().future_has_been_destroyed()) {
                    upsert_promises.pop_front();
                }
                while (!prefetch_promises.empty() &&
                       prefetch_promises.front().future_has_been_destroyed()) {
                    prefetch_promises.pop_front();
                }
                while (!traverse_promises.empty() &&
                       traverse_promises.front().future_has_been_destroyed()) {
                    traverse_promises.pop_front();
                }
                while (!move_trie_version_promises.empty() &&
                       move_trie_version_promises.front()
                           .future_has_been_destroyed()) {
                    move_trie_version_promises.pop_front();
                }
                if (!find_promises.empty() || !upsert_promises.empty() ||
                    !prefetch_promises.empty() || !traverse_promises.empty() ||
                    !move_trie_version_promises.empty()) {
                    did_nothing = false;
                }
                if (did_nothing) {
                    did_nothing_count++;
                }
                else {
                    did_nothing_count = 0;
                }
                if (did_nothing_count > 1000000) {
                    std::unique_lock g(parent->lock_);
                    sleeping.store(true, std::memory_order_release);
                    /* Very irritatingly, Boost.Fiber may have fibers scheduled
                     which weren't ready before, and if we sleep forever here
                     then they never run and cause anything waiting on them to
                     hang. So pulse Boost.Fiber every second at most for those
                     extremely rare occasions.
                     */
                    parent->cond_.wait_for(g, std::chrono::seconds(1), [this] {
                        return done.load(std::memory_order_acquire) ||
                               parent->comms_.size_approx() > 0;
                    });
                    sleeping.store(false, std::memory_order_release);
                }
            }
        }
    };

    std::unique_ptr<DbAsyncWorker> worker_;
    std::thread worker_thread_;
    UpdateAux *aux_;

    explicit OnDiskWithWorkerThreadImpl(OnDiskDbConfig const &options)
        : worker_thread_([&, options = options] {
            {
                std::unique_lock const g(lock_);
                worker_ = std::make_unique<DbAsyncWorker>(this, options);
                cond_.notify_one();
            }
            worker_->rwdb_run();
            std::unique_lock const g(lock_);
            worker_.reset();
        })
        , aux_([&] {
            std::unique_lock g(lock_);
            cond_.wait(g, [this] { return worker_ != nullptr; });
            return &(worker_->aux);
        }())
    {
    }

    explicit OnDiskWithWorkerThreadImpl(ReadOnlyOnDiskDbConfig const &options)
        : worker_thread_([&, options = options] {
            {
                std::unique_lock const g(lock_);
                worker_ = std::make_unique<DbAsyncWorker>(this, options);
                cond_.notify_one();
            }
            worker_->rodb_run(options.node_lru_size);
            std::unique_lock const g(lock_);
            worker_.reset();
        })
        , aux_([&] {
            std::unique_lock g(lock_);
            cond_.wait(g, [this] { return worker_ != nullptr; });
            return &(worker_->aux);
        }())
    {
    }

    ~OnDiskWithWorkerThreadImpl()
    {
        {
            std::unique_lock const g(lock_);
            worker_->done.store(true, std::memory_order_release);
            cond_.notify_one();
        }
        worker_thread_.join();
        aux_ = nullptr;
    }
}; // end OnDiskWorkerThreadImpl

#endif

class Db::RWOnDisk final : public Impl
{
    StateMachine &machine_;
    bool const compaction_;

    monad::storage::DbStorage db_storage_;
    UpdateAux aux_;
    Node *root_; // subtrie is owned by worker thread
    uint64_t root_version_{INVALID_BLOCK_NUM};
    uint64_t unflushed_version_{INVALID_BLOCK_NUM};

public:
    RWOnDisk(OnDiskDbConfig const &options, StateMachine &machine)
        : machine_{machine}
        , compaction_(options.compaction)
        , db_storage_{options.dbname_paths[0], options.append ? monad::storage::DbStorage::Mode::create_if_needed : monad::storage::DbStorage::Mode::truncate}
        , aux_{db_storage_, options.fixed_history_length}
        , root_{[&] {
            auto offset =
                aux_.get_root_offset_at_version(aux_.db_history_max_version());
            return offset != INVALID_OFFSET ? aux_.parse_node(offset) : nullptr;
        }()}
        , root_version_(aux_.db_history_max_version())
        , unflushed_version_{INVALID_BLOCK_NUM}
    {
    }

    virtual Node *root() override
    {
        return root_;
    }

    virtual UpdateAux &aux() override
    {
        return aux_;
    }

    UpdateAux const &aux() const
    {
        return aux_;
    }

    // threadsafe
    virtual find_cursor_result_type find_fiber_blocking(
        NodeCursor const & /*start */, NibblesView const & /* key */,
        uint64_t = 0) override
    {
        return {{}, find_result::root_node_is_null_failure};
    }

    // threadsafe
    virtual void upsert_fiber_blocking(
        UpdateList &&updates, uint64_t const version,
        bool const enable_compaction, bool const can_write_to_fast,
        bool const /*write_root*/) override
    {
        aux_.do_upsert(
            aux_.get_root_offset_at_version(version),
            machine_,
            std::move(updates),
            version,
            enable_compaction,
            can_write_to_fast);
    }

    virtual void move_trie_version_fiber_blocking(
        uint64_t const /*src*/, uint64_t const /*dest*/) override
    {
        // TODO
        MONAD_ABORT();
    }

    // threadsafe
    virtual size_t prefetch_fiber_blocking() override
    {
        return 0;
    }

    // threadsafe
    virtual bool traverse_fiber_blocking(
        Node & /*node*/, TraverseMachine & /*machine*/,
        uint64_t const /*version*/, size_t const /*concurrency_limit*/) override
    {
        // TODO
        MONAD_ABORT();
        return false;
    }

    virtual NodeCursor load_root_for_version(uint64_t const version) override
    {
        auto offset = aux_.get_root_offset_at_version(version);
        if (offset == INVALID_OFFSET) {
            return {};
        }
        auto node = aux_.parse_node(offset);
        return NodeCursor{*node};
    }

    virtual void copy_trie_fiber_blocking(
        uint64_t const /*src_version*/, NibblesView const /*src*/,
        uint64_t const /*dest_version*/, NibblesView const /*dest */,
        bool const /*blocked_by_write */) override
    {
        // TODO
        MONAD_ABORT();
    }

    virtual void update_finalized_version(uint64_t const version) override
    {
        aux().set_latest_finalized_version(version);
    }

    virtual void update_verified_version(uint64_t const version) override
    {
        MONAD_ASSERT(version <= aux().db_history_max_version());
        aux().set_latest_verified_version(version);
    }

    virtual uint64_t get_latest_finalized_version() const override
    {
        return aux().get_latest_finalized_version();
    }

    virtual uint64_t get_latest_verified_version() const override
    {
        return aux().get_latest_verified_version();
    }
};

struct RODb::Impl final
{
    storage::DbStorage db_storage_;
    UpdateAux aux_;

    Impl(ReadOnlyOnDiskDbConfig const &options)
        : db_storage_(
              options.dbname_paths[0], storage::DbStorage::Mode::open_existing)
        , aux_(db_storage_, std::nullopt)
    {
    }

    UpdateAux &aux()
    {
        return aux_;
    }

    find_cursor_result_type find_fiber_blocking(
        OwningNodeCursor /*start*/, NibblesView const & /*key*/,
        uint64_t const /*version*/)
    {
        // TODO
        MONAD_ABORT();
        return {{}, find_result::unknown};
    }

    OwningNodeCursor load_root_fiber_blocking(uint64_t version)
    {
        auto const root_offset = aux().get_root_offset_at_version(version);
        if (root_offset == INVALID_OFFSET) {
            return {};
        }
        return {*aux().parse_node(root_offset)};
    }
};

RODb::RODb(ReadOnlyOnDiskDbConfig const &options)
    : impl_(std::make_unique<Impl>(options))
{
}

RODb::~RODb() = default;

uint64_t RODb::get_latest_version() const
{
    MONAD_ASSERT(impl_);
    return impl_->aux().db_history_max_version();
}

uint64_t RODb::get_earliest_version() const
{
    MONAD_ASSERT(impl_);
    return impl_->aux().db_history_min_valid_version();
}

DbError find_result_to_db_error(find_result const result) noexcept
{
    switch (result) {
    case find_result::key_mismatch_failure:
    case find_result::branch_not_exist_failure:
    case find_result::key_ends_earlier_than_node_failure:
        return DbError::key_not_found;
    case find_result::root_node_is_null_failure:
    case find_result::version_no_longer_exist:
        return DbError::version_no_longer_exist;
    case find_result::unknown:
        return DbError::unknown;
    default:
        MONAD_ASSERT_PRINTF(
            false, "Unexpected find result: %d", static_cast<int>(result));
        return DbError::unknown;
    }
}

Result<OwningNodeCursor> RODb::find(
    OwningNodeCursor & /*node_cursor*/, NibblesView const /*key*/,
    uint64_t const /*block_id*/) const
{
    // TODO
    MONAD_ABORT();
    return DbError::unknown;
}

Result<OwningNodeCursor>
RODb::find(NibblesView const key, uint64_t const block_id) const
{
    MONAD_ASSERT(impl_);
    OwningNodeCursor cursor = impl_->load_root_fiber_blocking(block_id);
    return find(cursor, key, block_id);
}

#if 0
// TODO
Db::Db(StateMachine &machine)
    : impl_{std::make_unique<InMemory>(machine)}
{
}
#endif

Db::Db(StateMachine &machine, OnDiskDbConfig const &config)
    : impl_{std::make_unique<RWOnDisk>(config, machine)}
{
    MONAD_DEBUG_ASSERT(impl_->aux().is_on_disk());
}

Db::Db(ReadOnlyOnDiskDbConfig const &options)
    : impl_{std::make_unique<ROOnDiskBlocking>(options)}
{
    MONAD_DEBUG_ASSERT(impl_->aux().is_read_only());
}

#if 0
// TODO
Db::Db(AsyncIOContext &io_ctx)
    : impl_{std::make_unique<ROOnDiskBlocking>(io_ctx)}
{
}
#endif

Db::~Db() = default;

Result<NodeCursor>
Db::find(NodeCursor root, NibblesView const key, uint64_t const block_id) const
{
    MONAD_ASSERT(impl_);
    auto const [it, result] = impl_->find_fiber_blocking(root, key, block_id);
    if (result != find_result::success) {
        return find_result_to_db_error(result);
    }
    MONAD_DEBUG_ASSERT(it.node != nullptr);
    MONAD_DEBUG_ASSERT(it.node->has_value());
    return it;
}

NodeCursor Db::load_root_for_version(uint64_t const block_id) const
{
    MONAD_ASSERT(impl_);
    return impl_->load_root_for_version(block_id);
}

Result<NodeCursor>
Db::find(NibblesView const key, uint64_t const block_id) const
{
    MONAD_ASSERT(impl_);
    auto cursor = impl_->load_root_for_version(block_id);
    return find(cursor, key, block_id);
}

Result<byte_string_view>
Db::get(NibblesView const key, uint64_t const block_id) const
{
    auto res = find(key, block_id);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    if (!res.value().node->has_value()) {
        return DbError::key_not_found;
    }
    return res.value().node->value();
}

Result<byte_string_view> Db::get_data(
    NodeCursor root, NibblesView const key, uint64_t const block_id) const
{
    auto res = find(root, key, block_id);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);
    return res.value().node->data();
}

Result<byte_string_view>
Db::get_data(NibblesView const key, uint64_t const block_id) const
{
    auto res = find(key, block_id);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);
    return res.value().node->data();
}

void Db::upsert(
    UpdateList list, uint64_t const block_id, bool const enable_compaction,
    bool const can_write_to_fast, bool const write_root)
{
    MONAD_ASSERT(impl_);
    impl_->upsert_fiber_blocking(
        std::move(list),
        block_id,
        enable_compaction,
        can_write_to_fast,
        write_root);
}

void Db::copy_trie(
    uint64_t const src_version, NibblesView const src,
    uint64_t const dest_version, NibblesView const dest,
    bool const blocked_by_write)
{
    MONAD_ASSERT(impl_);
    impl_->copy_trie_fiber_blocking(
        src_version, src, dest_version, dest, blocked_by_write);
}

void Db::move_trie_version_forward(uint64_t const src, uint64_t const dest)
{
    MONAD_ASSERT(impl_);
    impl_->move_trie_version_fiber_blocking(src, dest);
    return;
}

bool Db::traverse(
    NodeCursor const cursor, TraverseMachine &machine, uint64_t const block_id,
    size_t const concurrency_limit)
{
    MONAD_ASSERT(impl_);
    MONAD_ASSERT(cursor.is_valid());
    return impl_->traverse_fiber_blocking(
        *cursor.node, machine, block_id, concurrency_limit);
}

bool Db::traverse_blocking(
    NodeCursor const /*cursor*/, TraverseMachine & /*machine*/,
    uint64_t const /*block_id*/)
{
    // TODO
    MONAD_ABORT();
    return false;
}

NodeCursor Db::root() const noexcept
{
    MONAD_ASSERT(impl_);
    return impl_->root() ? NodeCursor{*impl_->root()} : NodeCursor{};
}

void Db::update_finalized_version(uint64_t const version)
{
    MONAD_ASSERT(impl_);
    impl_->update_finalized_version(version);
}

void Db::update_verified_version(uint64_t const version)
{
    MONAD_ASSERT(impl_);
    impl_->update_verified_version(version);
}

void Db::update_voted_metadata(
    uint64_t const version, bytes32_t const &block_id)
{
    MONAD_ASSERT(impl_);
    impl_->aux().set_latest_voted(version, block_id);
}

uint64_t Db::get_latest_finalized_version() const
{
    MONAD_ASSERT(impl_);
    return impl_->get_latest_finalized_version();
}

uint64_t Db::get_latest_verified_version() const
{
    MONAD_ASSERT(impl_);
    return impl_->get_latest_verified_version();
}

bytes32_t Db::get_latest_voted_block_id() const
{
    MONAD_ASSERT(impl_);
    return impl_->aux().get_latest_voted_block_id();
}

uint64_t Db::get_latest_voted_version() const
{
    MONAD_ASSERT(impl_);
    return impl_->aux().get_latest_voted_version();
}

uint64_t Db::get_latest_version() const
{
    MONAD_ASSERT(impl_);
    if (impl_->aux().is_on_disk()) {
        return impl_->aux().db_history_max_version();
    }
    else {
        return impl_->root() ? 0 : INVALID_BLOCK_NUM;
    }
}

uint64_t Db::get_earliest_version() const
{
    MONAD_ASSERT(impl_);
    if (impl_->aux().is_on_disk()) {
        return impl_->aux().db_history_min_valid_version();
    }
    else {
        return impl_->root() ? 0 : INVALID_BLOCK_NUM;
    }
}

size_t Db::prefetch()
{
    MONAD_ASSERT(impl_);
    if (get_latest_version() == INVALID_BLOCK_NUM) {
        return 0;
    }
    return impl_->prefetch_fiber_blocking();
}

size_t Db::poll(bool const /*blocking*/, size_t const /*count*/)
{
    return 0;
}

bool Db::is_on_disk() const
{
    MONAD_ASSERT(impl_);
    return impl_->aux().is_on_disk();
}

bool Db::is_read_only() const
{
    MONAD_ASSERT(impl_);
    return is_on_disk() && impl_->aux().is_read_only();
}

uint64_t Db::get_history_length() const
{
    return is_on_disk() ? impl_->aux().version_history_length() : 1;
}

MONAD_MPT2_NAMESPACE_END
