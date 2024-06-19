#include <monad/fiber/priority_pool.hpp>

#include <monad/core/assert.h>
#include <monad/fiber/priority_algorithm.hpp>
#include <monad/fiber/priority_properties.hpp>
#include <monad/fiber/config.hpp>
#include <monad/fiber/priority_algorithm.hpp>
#include <monad/fiber/priority_properties.hpp>
#include <monad/fiber/priority_task.hpp>

#include <boost/fiber/operations.hpp>
#include <boost/fiber/properties.hpp>
#include <boost/fiber/protected_fixedsize_stack.hpp>
#include <boost/fiber/channel_op_status.hpp>
#include <boost/fiber/fiber.hpp>
#include <boost/fiber/mutex.hpp>
#include <boost/fiber/operations.hpp>
#include <boost/fiber/properties.hpp>

#include <cstdio>
#include <memory>
#include <mutex>
#include <thread>
#include <utility>

#include <pthread.h>

MONAD_FIBER_NAMESPACE_BEGIN


void PriorityPool::run_fiber_() noexcept
{
    working_++;

    while (true)
    {
        std::unique_ptr<monad_fiber_task_t, monad_fiber_task_deleter> pp;
        if ((channel_.read(pp) == EPIPE) || !pp)
            break;
        else
        {
            monad_fiber_current()->task.priority = pp->priority;
            pp->resume(pp.get());
        }
    }

    working_--;
}

PriorityPool::PriorityPool(unsigned const n_threads, unsigned const n_fibers)
    : sched_(n_threads)
{
    MONAD_ASSERT(n_threads);
    MONAD_ASSERT(n_fibers);

    fibers_.reserve(n_fibers);
    for (unsigned i = 0u; i < n_fibers; i++)
    {
        fibers_.emplace_back(
        monad_fiber_create(
            monad_fiber_default_stack_size,
            true,
            &sched_,
            +[](void * t){static_cast<PriorityPool*>(t)->run_fiber_();},
            this));
    }
}

PriorityPool::~PriorityPool()
{
    channel_.close();

    for (auto val = working_.load(); val != 0; val = working_)
        working_.wait(val);
}

MONAD_FIBER_NAMESPACE_END
