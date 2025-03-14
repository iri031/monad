#include <monad/fiber/priority_queue.hpp>

#include <monad/fiber/config.hpp>

#include <mutex>

MONAD_FIBER_NAMESPACE_BEGIN

bool PriorityQueue::empty() const
{
    std::lock_guard<std::mutex> const lock{mutex_};
    return queue_.empty();
}

context *PriorityQueue::pop()
{
    std::lock_guard<std::mutex> const lock{mutex_};
    context *ctx = nullptr;
    if (!queue_.empty()) {
        ctx = queue_.top();
        queue_.pop();
    }
    return ctx;
}

void PriorityQueue::push(context *const ctx)
{
    std::lock_guard<std::mutex> const lock{mutex_};
    queue_.push(ctx);
}

MONAD_FIBER_NAMESPACE_END
