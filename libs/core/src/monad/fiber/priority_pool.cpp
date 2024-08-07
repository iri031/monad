#include <monad/fiber/priority_pool.hpp>

#include <sys/mman.h>
#include <monad/core/assert.h>
#include <monad/fiber/config.hpp>

#include <cstdio>
#include <memory>
#include <thread>
#include <utility>

#include <pthread.h>
#include <unistd.h>

namespace {

constexpr size_t FIBER_STACK_SIZE = (1 << 21); // 2 MiB

monad_fiber_stack_t create_stack(size_t stack_size) {
    const size_t page_size = (size_t)getpagesize();
    monad_fiber_stack_t stack;
    stack.stack_base = mmap(nullptr, stack_size, PROT_READ | PROT_WRITE,
                            MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    // TODO(ken): we should also make guard pages to trap stack overflows
    if (stack.stack_base == MAP_FAILED) {
        throw std::system_error{errno, std::generic_category(),
                                "mmap(2) of fiber stack failed"};
    }
    if (mprotect(stack.stack_base, page_size, PROT_NONE) == -1) {
        throw std::system_error{errno, std::generic_category(),
                                "mprotect(2) of fiber stack guard page to PROT_NONE failed"};
    }
    stack.stack_bottom = static_cast<std::byte*>(stack.stack_base) + page_size;
    stack.stack_top = static_cast<std::byte*>(stack.stack_base) + stack_size;
    return stack;
}

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
    monad_fiber_channel_init(&task_channel_);
    spinlock_init(&channel_items_lock_);

    // Initialize our pool of fibers: set them to run the work-stealing
    // algorithm, and add them to the run queue
    for (unsigned i = 0; i < n_fibers; ++i) {
        monad_fiber_t &fiber = fibers_.emplace_back();
        monad_fiber_init(&fiber, create_stack(FIBER_STACK_SIZE));
        monad_fiber_set_entrypoint(&fiber, MONAD_FIBER_PRIO_LOWEST, fiber_main,
                                   std::bit_cast<uintptr_t>(&task_channel_));
        const int rc = monad_run_queue_push(run_queue_, &fiber);
        MONAD_ASSERT(rc == 0); // Run queue should always be big enough
    }

    // Initialize the worker threads that host fibers
    for (unsigned i = 0; i < n_threads; ++i) {
        auto thread = std::thread([this, i] {
            char name[16];
            std::snprintf(name, sizeof name, "worker_%02u", i);
            pthread_setname_np(pthread_self(), name);
            while (!done_.load(std::memory_order_acquire)) {
                // Get the highest priority fiber ready to run
                monad_fiber_t *const fiber = monad_run_queue_pop(run_queue_);
                if (fiber == nullptr)
                    continue; // Nothing is ready to run

                // Run the fiber until it suspends; the work-stealing fibers
                // never return
                (void)monad_fiber_run(fiber);
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
    for (const monad_fiber_t &fiber : fibers_) {
        const ptrdiff_t stack_size =
            static_cast<std::byte*>(fiber.stack.stack_top) -
            static_cast<std::byte*>(fiber.stack.stack_base);
        munmap(fiber.stack.stack_base, static_cast<size_t>(stack_size));
    }
}

void PriorityPool::submit(monad_fiber_prio_t priority,
                          std::function<void()> task) {
    spinlock_lock(&channel_items_lock_);
    TaskChannelItem &channel_item =
        channel_items_.emplace_back(monad_fiber_vbuf_t{}, this,
                                    PriorityTask{priority, std::move(task)});
    channel_item.self = --channel_items_.end();
    spinlock_unlock(&channel_items_lock_);
    const iovec iov = {std::addressof(channel_item), sizeof channel_item};
    monad_fiber_vbuf_init(&channel_item.vbuf, &iov);
    monad_fiber_channel_push(&task_channel_, &channel_item.vbuf);
}

MONAD_FIBER_NAMESPACE_END
