#pragma once

#include <monad/core/result.hpp>
#include <monad/fiber/algorithm.hpp>
#include <monad/fiber/config.hpp>
#include <monad/fiber/priority_queue.hpp>
#include <monad/fiber/priority_task.hpp>

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/condition_variable.hpp>
#include <boost/fiber/future/promise.hpp>
#include <boost/fiber/mutex.hpp>
#include <boost/outcome/try.hpp>

#include <functional>
#include <future>
#include <span>
#include <thread>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

class PriorityPool final
{
    PriorityQueue queue_{};

    bool done_{false};

    boost::fibers::mutex mutex_{};
    boost::fibers::condition_variable cv_{};

    std::vector<std::thread> threads_{};

    boost::fibers::buffered_channel<PriorityTask> channel_{1024};

    std::vector<boost::fibers::fiber> fibers_{};

    std::promise<void> start_{};

public:
    PriorityPool(
        unsigned n_threads, unsigned n_fibers, bool prevent_spin = false);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool();

    void submit(uint64_t const priority, std::function<void()> task)
    {
        channel_.push({priority, std::move(task)});
    }

    template <class Output1, class F>
    Result<
        std::vector<std::remove_reference_t<std::invoke_result_t<F, Output1>>>>
    submit_and_map(
        std::span<std::function<Result<Output1>()>> const tasks, F &&f)
    {
        // there is a race internal to the promise so the lifetime needs to
        // extend past this function
        std::shared_ptr<boost::fibers::promise<Result<Output1>>[]> promises{
            new boost::fibers::promise<Result<Output1>>[tasks.size()]};

        for (unsigned i = 0; i < tasks.size(); ++i) {
            submit(i, [i, promises, &task = tasks[i]] {
                promises[i].set_value(task());
            });
        }

        std::vector<std::remove_reference_t<std::invoke_result_t<F, Output1>>>
            ret{tasks.size()};
        BOOST_OUTCOME_TRY(fiber::map(
            std::span{promises.get(), tasks.size()}, f, std::span{ret}));
        return ret;
    }
};

MONAD_FIBER_NAMESPACE_END
