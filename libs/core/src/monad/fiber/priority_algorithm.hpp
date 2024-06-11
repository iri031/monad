#pragma once

#include <monad/fiber/config.hpp>
#include <monad/fiber/priority_properties.hpp>
#include <monad/fiber/priority_queue.hpp>

#include <boost/fiber/algo/algorithm.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/scheduler.hpp>

#include <chrono>

MONAD_FIBER_NAMESPACE_BEGIN

using boost::fibers::context;

class PriorityAlgorithm final
    : public boost::fibers::algo::algorithm_with_properties<PriorityProperties>
{
    PriorityQueue &rqueue_;

    using lqueue_type = boost::fibers::scheduler::ready_queue_type;

    lqueue_type lqueue_{};

public:
    explicit PriorityAlgorithm(PriorityQueue &);

    PriorityAlgorithm(PriorityAlgorithm const &) = delete;
    PriorityAlgorithm(PriorityAlgorithm &&) = delete;

    PriorityAlgorithm &operator=(PriorityAlgorithm const &) = delete;
    PriorityAlgorithm &operator=(PriorityAlgorithm &&) = delete;

    void awakened(context *, PriorityProperties &) noexcept override;

    context *pick_next() noexcept override;

    bool has_ready_fibers() const noexcept override;

    void suspend_until(
        std::chrono::steady_clock::time_point const &) noexcept override
    {
    }

    void notify() noexcept override {}
};

MONAD_FIBER_NAMESPACE_END
