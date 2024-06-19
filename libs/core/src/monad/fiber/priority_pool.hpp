#pragma once

#include <monad/fiber/config.hpp>
#include <monad/fiber/priority_queue.hpp>
#include <monad/fiber/priority_task.hpp>
#include <monad/fiber/wrappers.hpp>

#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/condition_variable.hpp>
#include <boost/fiber/mutex.hpp>

#include <future>
#include <thread>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

class PriorityPool final
{
    PriorityQueue queue_{};

    bool done_{false};

    boost::fibers::mutex mutex_{};
    boost::fibers::condition_variable cv_{};

    scheduler sched_;
    std::vector<std::thread> threads_{};

    struct monad_fiber_task_deleter
    {
        void operator()(monad_fiber_task_t *t) const
        {
            t->destroy(t);
        }
        void operator()(monad_fiber_t *t) const
        {
            (*this)(&t->task);
        }
    };

    channel<std::unique_ptr<monad_fiber_task_t, monad_fiber_task_deleter>> channel_{1024};
    std::vector<std::unique_ptr<monad_fiber_t,  monad_fiber_task_deleter>> fibers_;

    void run_fiber_() noexcept;
    std::atomic_size_t working_;

public:
    PriorityPool(unsigned n_threads, unsigned n_fibers);

    PriorityPool(PriorityPool const &) = delete;
    PriorityPool &operator=(PriorityPool const &) = delete;

    ~PriorityPool();

    template<typename Func>
    void submit(int64_t const priority, Func && func)
    {
        struct func_t : monad_fiber_task_t
        {
            func_t(int64_t const priority, Func && func)
                : monad_fiber_task_t{
                +[](monad_fiber_task_t * task){static_cast<struct func_t*>(task)->func();},
                +[](monad_fiber_task_t * task){delete static_cast<struct func_t*>(task);},
                priority
            }, func(std::forward<Func>(func)) {}
            std::decay_t<Func> func;
        };

        using pt = std::unique_ptr<monad_fiber_task_t, monad_fiber_task_deleter>;
        pt p{std::make_unique<func_t>(priority, std::forward<Func>(func)).release()};
        channel_.send(std::move(p));
    }
};

MONAD_FIBER_NAMESPACE_END
