#include <monad/fiber/priority_pool.hpp>

#include <sys/mman.h>
#include <monad/core/assert.h>
#include <monad/core/dump.hpp>
#include <monad/core/srcloc.hpp>
#include <monad/fiber/config.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/fiber_util.h>
#include <monad/fiber/run_queue.h>

#include <bit>
#include <cstdio>
#include <memory>
#include <source_location>
#include <thread>
#include <utility>

#include <pthread.h>

namespace {

constexpr size_t FIBER_STACK_SIZE = (1 << 21); // 2 MiB

// The work-stealing function run by all the fibers. It pulls TaskChannelItem
// instances from the task fiber channel and runs their PriorityTasks
[[noreturn]] uintptr_t fiber_main(uintptr_t fiber_arg) {
    auto *const task_channel = std::bit_cast<monad_fiber_channel_t*>(fiber_arg);
    while (true) {
        // Pop a value buffer from the fiber channel. This buffer contains
        // a TaskChannelItem
        monad_fiber_vbuf_t *const vbuf =
            monad_fiber_channel_pop(task_channel, MONAD_FIBER_PRIO_LOWEST);
        const iovec iov = monad_fiber_vbuf_data(vbuf);
        MONAD_ASSERT(iov.iov_len == sizeof(monad::fiber::TaskChannelItem));
        auto *const tci =
            static_cast<monad::fiber::TaskChannelItem*>(iov.iov_base);

        // Set our fiber priority to whatever the task tells us it's supposed
        // to be, then run the task
        monad_fiber_self()->priority = tci->prio_task.priority;
        tci->prio_task.task();

        // Tell the pool we're done with the task
        tci->pool->finish(tci->self);
    }
}

} // anonymous namespace

MONAD_FIBER_NAMESPACE_BEGIN

PriorityPool::PriorityPool(unsigned const n_threads, unsigned const n_fibers)
{
    MONAD_ASSERT(n_threads > 0);
    MONAD_ASSERT(n_fibers > 0);

    threads_.reserve(n_threads);
    monad_run_queue_create(n_fibers, &run_queue_); // XXX: check return code
    monad_fiber_channel_init(&task_channel_,
                             make_srcloc(std::source_location::current()));
    monad_fiber_channel_set_name(&task_channel_, "task_chan");
    monad_spinlock_init(&channel_items_lock_);

    // Initialize our pool of fibers: set them to run the work-stealing
    // algorithm, and add them to the run queue
    char namebuf[MONAD_FIBER_NAME_LEN + 1];
    for (unsigned i = 0; i < n_fibers; ++i) {
        monad_fiber_stack_t fiber_stack;
        size_t fiber_stack_size = FIBER_STACK_SIZE;
        if (int rc = monad_fiber_alloc_stack(&fiber_stack_size, &fiber_stack)) {
            throw std::system_error{rc, std::generic_category(),
                    "unable to allocate fiber stack memory region"};
        }

        monad_fiber_t &fiber = fibers_.emplace_back();
        monad_fiber_init(&fiber, fiber_stack);
        monad_fiber_set_function(&fiber, MONAD_FIBER_PRIO_LOWEST, fiber_main,
                                 std::bit_cast<uintptr_t>(&task_channel_));
        snprintf(namebuf, sizeof namebuf, "F%03d", i);
        (void)monad_fiber_set_name(&fiber, namebuf);
        monad_fiber_debug_add(&fiber);
        const int rc = monad_run_queue_try_push(run_queue_, &fiber);
        MONAD_ASSERT(rc == 0); // Run queue should always be big enough
    }

    // Initialize the worker threads that host fibers
    for (unsigned i = 0; i < n_threads; ++i) {
        auto thread = std::thread([this, i] {
            char name[16];
            int rc;
            std::snprintf(name, sizeof name, "worker_%02u", i);
            pthread_setname_np(pthread_self(), name);
            while (!done_.load(std::memory_order_acquire)) {
                // Get the highest priority fiber ready to run
                monad_fiber_t *const fiber = monad_run_queue_try_pop(run_queue_);
                if (fiber == nullptr)
                    continue; // Nothing is ready to run

                // Run the fiber until it suspends; the work-stealing fibers
                // never return
                rc = monad_fiber_run(fiber, nullptr);
                MONAD_ASSERT(rc == 0);
            }
        });
        threads_.push_back(std::move(thread));
    }
}

PriorityPool::~PriorityPool()
{
    done_ = true;
    while (threads_.size()) {
        auto &thread = threads_.back();
        thread.join();
        threads_.pop_back();
    }
    monad_run_queue_destroy(run_queue_);
    for (monad_fiber_t &fiber : fibers_) {
        monad_fiber_debug_remove(&fiber);
        monad_fiber_free_stack(fiber.stack);
    }
}

void PriorityPool::submit(monad_fiber_prio_t priority,
                          std::function<void()> task) {
    monad_spinlock_lock(&channel_items_lock_);
    ++channel_items_stats_.total_tasks;
    TaskChannelItem &channel_item =
        channel_items_.emplace_back(monad_fiber_vbuf_t{}, this,
                                    PriorityTask{priority, std::move(task)});
    channel_item.self = --channel_items_.end();
    monad_spinlock_unlock(&channel_items_lock_);
    const iovec iov = {std::addressof(channel_item), sizeof channel_item};
    monad_fiber_vbuf_init(&channel_item.vbuf, &iov);
    monad_fiber_channel_push(&task_channel_, &channel_item.vbuf);
}

void PriorityPool::print_stats(monad_dump_ctx_t *pool_ctx, bool dump_fibers) {
    monad_dump_println(pool_ctx, "priority pool %p statistics:", this);
    monad_dump_println(pool_ctx, "channel tasks submitted: %zu",
                       channel_items_stats_.total_tasks);

    {
        const raii_dump_ctx rctx{pool_ctx, "monad_run_queue %p stats:",
                                 run_queue_};
        monad_run_queue_dump_stats(run_queue_, rctx.get());
    }

    if (dump_fibers) {
        monad_dump_println(pool_ctx, "stats for %zu fibers:", fibers_.size());
        for (unsigned i = 0; const monad_fiber_t &fiber : fibers_) {
            const raii_dump_ctx rctx{pool_ctx, "* FIBER %u", i++};
            monad_fiber_dump(&fiber, rctx.get());
        }
    }
}

MONAD_FIBER_NAMESPACE_END
