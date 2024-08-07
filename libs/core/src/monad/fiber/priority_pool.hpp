#pragma once

#include <monad/core/spinlock.h>
#include <monad/fiber/config.hpp>
#include <monad/fiber/future.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/run_queue.h>
#include <monad/fiber/priority_task.hpp>

#include <atomic>
#include <deque>
#include <functional>
#include <list>
#include <thread>
#include <vector>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

class PriorityPool;

// A PriorityTask, plus additional book-keeping fields to help manage its memory
// and allow it to be linked onto a fiber channel
struct TaskChannelItem {
    using token_t = std::list<TaskChannelItem>::const_iterator;

    monad_fiber_vbuf_t vbuf; ///< vbuf header to link us onto a channel
    PriorityPool *pool;      ///< Pool we live in
    PriorityTask prio_task;  ///< The task itself
    token_t self;            ///< Reference to ourselves, from pool perspective
};

class PriorityPool final
{
    monad_run_queue_t *run_queue_{};
    monad_fiber_channel_t task_channel_{};
    std::vector<std::thread> threads_{};
    std::deque<monad_fiber_t> fibers_{};
    std::atomic<bool> done_{false};
    alignas(64) spinlock_t channel_items_lock_;
    std::list<TaskChannelItem> channel_items_;

public:
    PriorityPool(unsigned n_threads, unsigned n_fibers);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool();

    // Submit a task to the fiber pool
    void submit(monad_fiber_prio_t priority, std::function<void()> task);

    // Called by the fiber to mark that the task is finished
    void finish(TaskChannelItem::token_t finished) {
        spinlock_lock(&channel_items_lock_);
        channel_items_.erase(finished); // Reclaim the memory
        spinlock_unlock(&channel_items_lock_);
    }
};

MONAD_FIBER_NAMESPACE_END
