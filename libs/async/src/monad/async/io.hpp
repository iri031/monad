#pragma once

/* Current AsyncIO:
./benchmark_io_test_main --storage /dev/mapper/raid0-rawblk1 --workload 0
--concurrent-io 64 --eager-completions

Total ops/sec: 227811 mean latency: 87335.5 min: 20310 max: 909019

./benchmark_io_test_main --storage /dev/mapper/raid0-rawblk1 --workload 0
--concurrent-io 64 --eager-completions --kernel-poll-thread 15

Total ops/sec: 289950 mean latency: 217287 min: 48521 max: 742049


This wrapper of the new i/o executor:

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--concurrent-io 64

Total ops/sec: 137692 mean latency: 93132 min: 22471 max: 391000

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--concurrent-io 64 --kernel-poll-thread 15

Total ops/sec: 301711 mean latency: 176930 min: 35361 max: 1.21906e+06

This is 4% faster for the SQPOLL edition. The syscall edition is vastly
slower which is surprising, about 43% slower, despite that the native backend
with syscall config has expected performance.


Natively on the new i/o executor:

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--concurrent-io 64  --new-io-executor

Total ops/sec: 293904 mean latency: 216994 min: 33610 max: 8.38653e+06

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--concurrent-io 64 --kernel-poll-thread 15 --new-io-executor

Total ops/sec: 298948 mean latency: 213808 min: 36710 max: 8.30234e+06

It cannot be possible that the native backend is slower than the AsyncIO wrap of
the native backend. Something is wrong here.
*/

#include <monad/async/connected_operation.hpp>

#include <monad/async/cpp_helpers.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/executor.h>
#include <monad/async/file_io.h>
#include <monad/async/storage_pool.hpp>
#include <monad/async/task.h>
#include <monad/context/context_switcher.h>

#include <monad/core/unordered_map.hpp>

#include <monad/io/buffer_pool.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>

#include <monad/mem/allocators.hpp>

#include <atomic>
#include <cassert>
#include <cstddef>
#include <deque>
#include <filesystem>
#include <span>
#include <tuple>
#include <type_traits>

MONAD_ASYNC_NAMESPACE_BEGIN

class read_single_buffer_sender;

// helper struct that records IO stats
struct IORecord
{
    unsigned inflight_rd{0};
    unsigned inflight_rd_scatter{0};
    unsigned inflight_wr{0};
    unsigned inflight_tm{0};
    std::atomic<unsigned> inflight_ts{0};

    unsigned max_inflight_rd{0};
    unsigned max_inflight_rd_scatter{0};
    unsigned max_inflight_wr{0};

    unsigned nreads{0};
    // Reads and scatter reads which got a EAGAIN and were retried
    unsigned reads_retried{0};
};

class AsyncIO final
{
public:
    struct timed_invocation_state;

private:
    friend class read_single_buffer_sender;
    using _storage_pool = class storage_pool;
    using cnv_chunk = _storage_pool::cnv_chunk;
    using seq_chunk = _storage_pool::seq_chunk;

    template <class T>
    struct chunk_ptr_
    {
        std::shared_ptr<T> ptr;
        int read_fd{-1}, write_fd{-1};
        std::shared_ptr<monad_async_file_head> io_uring_read_fd,
            io_uring_write_fd;

        constexpr chunk_ptr_() = default;

        constexpr chunk_ptr_(std::shared_ptr<T> ptr_)
            : ptr(std::move(ptr_))
            , read_fd(ptr ? ptr->read_fd().first : -1)
            , write_fd(ptr ? ptr->write_fd(0).first : -1)
        {
        }
    };

    monad_async_executor_attr executor_attr_;
    monad::async::executor_ptr executor_;
    monad::context::context_switcher_ptr context_switcher_;
    monad::async::task_ptr dispatch_task_;

    struct task_pool_item_
    {
        AsyncIO *const parent;
        task_ptr task;
        unsigned counter{0};

        struct erased_invocable
        {
            virtual ~erased_invocable() {}

            virtual monad_c_result operator()(monad_async_task task) = 0;

        } *current_work{nullptr};

        std::byte work_storage[64];

        constexpr explicit task_pool_item_(AsyncIO *parent_, task_ptr task_)
            : parent(parent_)
            , task(std::move(task_))
        {
        }

        task_pool_item_(task_pool_item_ const &) = delete;
        task_pool_item_(task_pool_item_ &&) = delete;

        ~task_pool_item_()
        {
            if (current_work != nullptr) {
                current_work->~erased_invocable();
            }
        }

        template <class T>
        struct invocable final : public erased_invocable
        {
            T v;

            template <class U>
            explicit invocable(U &&f)
                : v(std::forward<U>(f))
            {
            }

            virtual monad_c_result operator()(monad_async_task task) override
            {
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>
                    ret{v(task)};
                return ret ? monad_c_make_success(ret.assume_value())
                           : monad_c_make_failure(
                                 (int)ret.assume_error().value());
            }
        };

        template <class F>
            requires(
                std::is_invocable_v<F, monad_async_task> &&
                std::is_constructible_v<
                    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                        intptr_t>,
                    std::invoke_result_t<F, monad_async_task>>)
        void emplace(F &&v)
        {
            static_assert(
                sizeof(invocable<F>) <= sizeof(work_storage),
                "sizeof(erased_invocable) > sizeof(work_storage)");
            current_work = new (work_storage) invocable<F>(std::forward<F>(v));
            task->derived.user_ptr = this;
        }
    };

    std::vector<std::unique_ptr<task_pool_item_>> task_pool_sleeping_;

    std::mutex threadsafe_invocations_lock_;
    std::deque<erased_connected_operation *> threadsafe_invocations_;

    pid_t const owning_tid_;
    class storage_pool *storage_pool_{nullptr};
    chunk_ptr_<cnv_chunk> cnv_chunk_;
    std::vector<chunk_ptr_<seq_chunk>> seq_chunks_;

    bool capture_io_latencies_{false};

    // IO records
    IORecord records_;

    static monad_c_result task_pool_trampoline_(monad_context_task task_)
    {
        auto *task = ((monad_async_task)task_);
        auto *self = (task_pool_item_ *)task->derived.user_ptr;
        assert(task == self->task.get());
        auto ret = (*self->current_work)(task);
        task->derived.user_code = nullptr;
        task->derived.user_ptr = nullptr;
        self->current_work->~erased_invocable();
        self->current_work = nullptr;
        self->counter++;
        self->parent->task_pool_sleeping_.emplace_back(self);
        return ret;
    }

    template <class U>
        requires(std::is_invocable_v<U>)
    void submit_request_within_task_(U &&f, bool force_launch_on_pool = false);

    void submit_request_(
        filled_read_buffer &buffer, chunk_offset_t chunk_and_offset,
        void *uring_data, enum erased_connected_operation::io_priority prio);
    void submit_request_(
        std::span<const struct iovec> buffers, chunk_offset_t chunk_and_offset,
        void *uring_data, enum erased_connected_operation::io_priority prio);
    void submit_request_(
        std::span<std::byte const> buffer, chunk_offset_t chunk_and_offset,
        void *uring_data, enum erased_connected_operation::io_priority prio);
    void submit_request_(timed_invocation_state *state, void *uring_data);

    void
    invoke_completed_(erased_connected_operation *state, result<size_t> res);
    static monad_c_result dispatch_task_impl_(monad_context_task task) noexcept;
    bool poll_uring_(bool blocking);

public:
    // API to enable transition to new i/o executor
    monad_async_executor tr_executor() const
    {
        return executor_.get();
    }

    monad_context_switcher tr_context_switcher() const
    {
        return context_switcher_.get();
    }

    void tr_submit_request(
        monad_async_io_status *iostatus, monad_async_task task,
        struct monad_async_task_registered_io_buffer &tofill, size_t bytes,
        chunk_offset_t chunk_and_offset);
    void tr_submit_request(
        monad_async_io_status *iostatus, monad_async_task task,
        std::span<const struct iovec> buffers, chunk_offset_t chunk_and_offset);
    void tr_submit_request(
        monad_async_io_status *iostatus, monad_async_task task,
        std::span<std::byte> buffer, int buffer_index,
        chunk_offset_t chunk_and_offset) =
        delete; // prevent use of read overload
    void tr_submit_request(
        monad_async_io_status *iostatus, monad_async_task task,
        std::span<std::byte const> buffer, int buffer_index,
        chunk_offset_t chunk_and_offset);

    template <class F, class... Args>
        requires(
            std::is_invocable_v<F, monad_async_task> &&
            std::is_constructible_v<
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>,
                std::invoke_result_t<F, monad_async_task>>)
    auto tr_launch_on_task_from_pool(F &&f)
    {
        std::unique_ptr<task_pool_item_> item;
        if (!task_pool_sleeping_.empty()) {
            for (auto it = task_pool_sleeping_.rbegin();
                 it != task_pool_sleeping_.rend();
                 ++it) {
                if ((*it)->task->current_executor.load(
                        std::memory_order_acquire) == nullptr) {
                    std::swap(*it, task_pool_sleeping_.back());
                    item = std::move(task_pool_sleeping_.back());
                    task_pool_sleeping_.pop_back();
                    break;
                }
            }
        }
        if (!item) {
            monad_async_task_attr task_attr{{.stack_size = 256 * 1024}};
            item = std::make_unique<task_pool_item_>(
                this,
                monad::async::make_task(context_switcher_.get(), task_attr));
        }
        to_result(monad_async_task_set_priorities(
                      item->task.get(),
                      monad_async_priority_low,
                      monad_async_priority_unchanged))
            .value();
        item->task->derived.user_code = task_pool_trampoline_;
        item->emplace(std::move(f));
        to_result(
            monad_async_task_attach(executor_.get(), item->task.get(), nullptr))
            .value();
        auto *tpi = item.release();
        return
            [tpi, counter = tpi->counter]() { return tpi->counter == counter; };
    }

public:
    AsyncIO(
        class storage_pool &pool, monad::io::Buffers &rwbuf,
        unsigned max_io_concurrency = 0);

    ~AsyncIO();

    pid_t owning_thread_id() const noexcept
    {
        return owning_tid_;
    }

    bool is_read_only() const noexcept
    {
        return executor_attr_.io_uring_wr_ring.entries == 0;
    }

    class storage_pool &storage_pool() noexcept
    {
        MONAD_DEBUG_ASSERT(storage_pool_ != nullptr);
        return *storage_pool_;
    }

    const class storage_pool &storage_pool() const noexcept
    {
        MONAD_DEBUG_ASSERT(storage_pool_ != nullptr);
        return *storage_pool_;
    }

    size_t chunk_count() const noexcept
    {
        return seq_chunks_.size();
    }

    file_offset_t chunk_capacity(size_t id) const noexcept
    {
        MONAD_ASSERT_PRINTF(
            id < seq_chunks_.size(),
            "id %zu seq chunks size %zu",
            id,
            seq_chunks_.size());
        return seq_chunks_[id].ptr->capacity();
    }

    //! The instance for this thread
    static AsyncIO *thread_instance() noexcept
    {
        return detail::AsyncIO_thread_instance();
    }

    unsigned io_in_flight() const noexcept
    {
        return records_.inflight_rd + records_.inflight_rd_scatter +
               records_.inflight_wr + records_.inflight_tm +
               records_.inflight_ts.load(std::memory_order_relaxed) +
               deferred_initiations_in_flight();
    }

    unsigned reads_in_flight() const noexcept
    {
        return records_.inflight_rd;
    }

    unsigned max_reads_in_flight() const noexcept
    {
        return records_.max_inflight_rd;
    }

    unsigned reads_scatter_in_flight() const noexcept
    {
        return records_.inflight_rd_scatter;
    }

    unsigned max_reads_scatter_in_flight() const noexcept
    {
        return records_.max_inflight_rd_scatter;
    }

    unsigned writes_in_flight() const noexcept
    {
        return records_.inflight_wr;
    }

    unsigned max_writes_in_flight() const noexcept
    {
        return records_.max_inflight_wr;
    }

    unsigned timers_in_flight() const noexcept
    {
        return records_.inflight_tm;
    }

    unsigned deferred_initiations_in_flight() const noexcept;

    unsigned threadsafeops_in_flight() const noexcept
    {
        return records_.inflight_ts.load(std::memory_order_relaxed);
    }

    bool capture_io_latencies() const noexcept
    {
        return capture_io_latencies_;
    }

    void set_capture_io_latencies(bool v) noexcept
    {
        capture_io_latencies_ = v;
    }

    // Useful for taking a copy of anonymous inode files used by the unit tests
    void dump_fd_to(size_t which, std::filesystem::path const &path);

    // Blocks until at least one completion is processed, returning number
    // of completions processed.
    size_t poll_blocking(size_t count = 1)
    {
        size_t n = 0;
        for (; n < count; n++) {
            if (!poll_uring_(n == 0)) {
                break;
            }
        }
        return n;
    }

    std::optional<size_t>
    poll_blocking_if_not_within_completions(size_t count = 1)
    {
        if (detail::AsyncIO_per_thread_state().am_within_completions()) {
            return std::nullopt;
        }
        return poll_blocking(count);
    }

    // Never blocks
    size_t poll_nonblocking(size_t count = size_t(-1))
    {
        size_t n = 0;
        for (; n < count; n++) {
            if (!poll_uring_(false)) {
                break;
            }
        }
        return n;
    }

    std::optional<size_t>
    poll_nonblocking_if_not_within_completions(size_t = size_t(-1))
    {
        // We are never in completions in the new i/o executor wrap
        return std::nullopt;
    }

    void wait_until_done()
    {
        while (io_in_flight() > 0) {
            poll_blocking(size_t(-1));
        }
    }

    void flush()
    {
        wait_until_done();
    }

    void reset_records()
    {
        records_.max_inflight_rd = 0;
        records_.max_inflight_rd_scatter = 0;
        records_.max_inflight_wr = 0;
        records_.nreads = 0;
    }

    size_t submit_read_request(
        filled_read_buffer &buffer, chunk_offset_t offset,
        erased_connected_operation *uring_data)
    {
        submit_request_(buffer, offset, uring_data, uring_data->io_priority());
        if (++records_.inflight_rd > records_.max_inflight_rd) {
            records_.max_inflight_rd = records_.inflight_rd;
        }
        ++records_.nreads;
        return size_t(-1); // we never complete immediately
    }

    size_t submit_read_request(
        std::span<const struct iovec> buffers, chunk_offset_t offset,
        erased_connected_operation *uring_data)

    {
        submit_request_(buffers, offset, uring_data, uring_data->io_priority());
        if (++records_.inflight_rd_scatter > records_.max_inflight_rd_scatter) {
            records_.max_inflight_rd_scatter = records_.inflight_rd_scatter;
        }
        ++records_.nreads;
        return size_t(-1); // we never complete immediately
    }

    void submit_write_request(
        std::span<std::byte const> buffer, chunk_offset_t offset,
        erased_connected_operation *uring_data)
    {
        submit_request_(buffer, offset, uring_data, uring_data->io_priority());
        if (++records_.inflight_wr > records_.max_inflight_wr) {
            records_.max_inflight_wr = records_.inflight_wr;
        }
    }

    // WARNING: Must exist until completion!
    struct timed_invocation_state
    {
        struct __kernel_timespec ts
        {
            0, 0
        };

        bool timespec_is_absolute{false};
        bool timespec_is_utc_clock{false};
    };

    void submit_timed_invocation_request(
        timed_invocation_state *info, erased_connected_operation *uring_data)
    {
        submit_request_(info, uring_data);
        ++records_.inflight_tm;
    }

    void submit_threadsafe_invocation_request(
        erased_connected_operation *uring_data);

    /* This isn't the ideal place to put this, but only AsyncIO knows how to
    get i/o buffers into which to place connected i/o states.
    */
    static constexpr size_t MAX_CONNECTED_OPERATION_SIZE = DISK_PAGE_SIZE;
    static constexpr size_t READ_BUFFER_SIZE = 8 * DISK_PAGE_SIZE;
    static constexpr size_t WRITE_BUFFER_SIZE = 8 * 1024 * 1024;
    static constexpr size_t MONAD_IO_BUFFERS_READ_SIZE = READ_BUFFER_SIZE;
    static constexpr size_t MONAD_IO_BUFFERS_WRITE_SIZE = WRITE_BUFFER_SIZE;

private:
    struct connected_operation_storage_
    {
        std::byte v[MAX_CONNECTED_OPERATION_SIZE];
    };

    using connected_operation_storage_allocator_type_ =
        allocators::malloc_free_allocator<connected_operation_storage_>;

    connected_operation_storage_allocator_type_
        connected_operation_storage_pool_;

public:
    // Only used with write ops
    template <class ConnectedOperationType>
    struct registered_io_buffer_with_connected_operation
    {
        alignas(DMA_PAGE_SIZE) std::byte write_buffer[WRITE_BUFFER_SIZE];

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
        ConnectedOperationType state[0];
#pragma GCC diagnostic pop

        constexpr registered_io_buffer_with_connected_operation() {}
    };
    friend struct io_connected_operation_unique_ptr_deleter;

    struct io_connected_operation_unique_ptr_deleter
    {
        void operator()(erased_connected_operation *p) const
        {
            auto *io = p->executor();
            p->~erased_connected_operation();
#ifndef NDEBUG
            memset((void *)p, 0xff, MAX_CONNECTED_OPERATION_SIZE);
#endif
            using traits = std::allocator_traits<
                connected_operation_storage_allocator_type_>;
            traits::deallocate(
                io->connected_operation_storage_pool_,
                (connected_operation_storage_ *)p,
                1);
        }
    };

    using erased_connected_operation_unique_ptr_type = std::unique_ptr<
        erased_connected_operation, io_connected_operation_unique_ptr_deleter>;
    template <sender Sender, receiver Receiver>
    using connected_operation_unique_ptr_type = std::unique_ptr<
        decltype(connect(
            std::declval<AsyncIO &>(), std::declval<Sender>(),
            std::declval<Receiver>())),
        io_connected_operation_unique_ptr_deleter>;

    void do_free_read_buffer(std::byte *b, int index) noexcept
    {
        (void)b;
#ifndef NDEBUG
        memset((void *)b, 0xff, READ_BUFFER_SIZE);
#endif
        monad_async_task task =
            executor_->current_task.load(std::memory_order_acquire);
        if (task == nullptr) {
            // This is wrong, but gets us working as
            // monad_async_task_release_registered_io_buffer() just happens to
            // not use task except to fetch its executor
            task = dispatch_task_.get();
        }
        to_result(monad_async_task_release_registered_io_buffer(task, index))
            .value();
    }

    void do_free_write_buffer(std::byte *b, int index) noexcept
    {
        (void)b;
#ifndef NDEBUG
        static_assert(WRITE_BUFFER_SIZE >= CPU_PAGE_SIZE);
        memset((void *)b, 0xff, CPU_PAGE_SIZE);
#endif
        monad_async_task task =
            executor_->current_task.load(std::memory_order_acquire);
        if (task == nullptr) {
            // This is wrong, but gets us working as
            // monad_async_task_release_registered_io_buffer() just happens to
            // not use task except to fetch its executor
            task = dispatch_task_.get();
        }
        to_result(monad_async_task_release_registered_io_buffer(task, index))
            .value();
    }

    using read_buffer_ptr = detail::read_buffer_ptr;
    using write_buffer_ptr = detail::write_buffer_ptr;

    write_buffer_ptr get_write_buffer() noexcept
    {
        monad_async_task_registered_io_buffer buffer{};
        auto *task = executor_->current_task.load(std::memory_order_acquire);
        if (task == nullptr) {
            buffer = poll_uring_while_no_io_write_buffers_();
        }
        else {
            to_result(monad_async_task_claim_registered_file_io_write_buffer(
                          &buffer, task, WRITE_BUFFER_SIZE, {}))
                .value();
        }
        return write_buffer_ptr(
            (std::byte *)buffer.iov[0].iov_base,
            detail::write_buffer_deleter(this, buffer.index));
    }

private:
    monad_async_task_registered_io_buffer
    poll_uring_while_no_io_write_buffers_();

    template <bool is_write, class F>
    auto make_connected_impl_(F &&connect)
    {
        using connected_type = decltype(connect());
        static_assert(sizeof(connected_type) <= MAX_CONNECTED_OPERATION_SIZE);
        using traits =
            std::allocator_traits<connected_operation_storage_allocator_type_>;
        unsigned char *mem = (unsigned char *)traits::allocate(
            connected_operation_storage_pool_, 1);
        MONAD_ASSERT_PRINTF(
            mem != nullptr, "failed due to %s", strerror(errno));
        MONAD_DEBUG_ASSERT(((void)mem[0], true));
        auto ret = std::unique_ptr<
            connected_type,
            io_connected_operation_unique_ptr_deleter>(
            new (mem) connected_type(connect()));
        // Did you accidentally pass in a foreign buffer to use?
        // Can't do that, must use buffer returned.
        MONAD_DEBUG_ASSERT(ret->sender().buffer().data() == nullptr);
        if constexpr (is_write) {
            auto buffer = std::move(ret->sender()).buffer();
            buffer.set_write_buffer(get_write_buffer());
            ret->sender().reset(ret->sender().offset(), std::move(buffer));
        }
        return ret;
    }

public:
    //! Construct into internal memory a connected state for an i/o read
    //! or write (not timed delay)
    template <sender Sender, receiver Receiver>
        requires(
            (Sender::my_operation_type == operation_type::read ||
             Sender::my_operation_type == operation_type::write) &&
            requires(
                Receiver r, erased_connected_operation *o,
                typename Sender::result_type x) {
                r.set_value(o, std::move(x));
            })
    auto make_connected(Sender &&sender, Receiver &&receiver)
    {
        return make_connected_impl_<
            Sender::my_operation_type == operation_type::write>([&] {
            return connect<Sender, Receiver>(
                *this, std::move(sender), std::move(receiver));
        });
    }

    //! Construct into internal memory a connected state for an i/o read
    //! or write (not timed delay)
    template <
        sender Sender, receiver Receiver, class... SenderArgs,
        class... ReceiverArgs>
        requires(
            (Sender::my_operation_type == operation_type::read ||
             Sender::my_operation_type == operation_type::write) &&
            requires(
                Receiver r, erased_connected_operation *o,
                typename Sender::result_type x) {
                r.set_value(o, std::move(x));
            } &&
            std::is_constructible_v<Sender, SenderArgs...> &&
            std::is_constructible_v<Receiver, ReceiverArgs...>)
    auto make_connected(
        std::piecewise_construct_t _, std::tuple<SenderArgs...> &&sender_args,
        std::tuple<ReceiverArgs...> &&receiver_args)
    {
        return make_connected_impl_<
            Sender::my_operation_type == operation_type::write>([&] {
            return connect<Sender, Receiver>(
                *this, _, std::move(sender_args), std::move(receiver_args));
        });
    }

    template <class Base, sender Sender, receiver Receiver>
    void notify_operation_initiation_success_(
        detail::connected_operation_storage<Base, Sender, Receiver> *state)
    {
        (void)state;
#if MONAD_TRIE_ENABLE_WRITEBACK_CACHE
        if constexpr (detail::connected_operation_storage<
                          Base,
                          Sender,
                          Receiver>::is_write()) {
            auto *p =
                erased_connected_operation::rbtree_node_traits::to_node_ptr(
                    state);
            erased_connected_operation::rbtree_node_traits::set_key(
                p, state->sender().offset().raw());
            MONAD_DEBUG_ASSERT(p->key == state->sender().offset().raw());
            extant_write_operations_::init(p);
            auto pred = [](auto const *a, auto const *b) {
                auto get_key = [](auto const *a) {
                    return erased_connected_operation::rbtree_node_traits::
                        get_key(a);
                };
                return get_key(a) > get_key(b);
            };
            extant_write_operations_::insert_equal_lower_bound(
                &extant_write_operations_header_, p, pred);
        }
#endif
    }

    template <class Base, sender Sender, receiver Receiver>
    void notify_operation_reset_(
        detail::connected_operation_storage<Base, Sender, Receiver> *state)
    {
        (void)state;
    }

    template <class Base, sender Sender, receiver Receiver, class T>
    void notify_operation_completed_(
        detail::connected_operation_storage<Base, Sender, Receiver> *state,
        result<T> &res)
    {
        (void)state;
        (void)res;
#if MONAD_TRIE_ENABLE_WRITEBACK_CACHE
        if constexpr (detail::connected_operation_storage<
                          Base,
                          Sender,
                          Receiver>::is_write()) {
            extant_write_operations_::erase(
                &extant_write_operations_header_,
                erased_connected_operation::rbtree_node_traits::to_node_ptr(
                    state));
        }
        else if constexpr (
            detail::connected_operation_storage<Base, Sender, Receiver>::
                is_read() &&
            !std::is_void_v<T>) {
            if (res && res.assume_value() > 0) {
                // If we filled the data from extant write buffers above,
                // adjust bytes transferred to account for that.
                res = success(
                    res.assume_value() +
                    erased_connected_operation::rbtree_node_traits::get_key(
                        state));
            }
        }
#endif
    }

private:
    using extant_write_operations_ = ::boost::intrusive::rbtree_algorithms<
        erased_connected_operation::rbtree_node_traits>;
    erased_connected_operation::rbtree_node_traits::node
        extant_write_operations_header_;
};

using erased_connected_operation_ptr =
    AsyncIO::erased_connected_operation_unique_ptr_type;

static_assert(sizeof(AsyncIO) == 656);
static_assert(alignof(AsyncIO) == 8);

namespace detail
{
    inline void read_buffer_deleter::operator()(std::byte *b)
    {
        parent_->do_free_read_buffer(b, index_);
    }

    inline void write_buffer_deleter::operator()(std::byte *b)
    {
        parent_->do_free_write_buffer(b, index_);
    }
}

MONAD_ASYNC_NAMESPACE_END
