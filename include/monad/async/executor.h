#pragma once

#include "config.h"

#include <liburing.h>

// Must come after <liburing.h>, otherwise breaks build on clang
#include <stdatomic.h>

#include "task.h"

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief The public attributes of an executor
typedef struct monad_async_executor_head
{
    // The following are not user modifiable
#ifdef __cplusplus
    // C++ is difficult here and requires std::
    std::atomic<monad_async_task> current_task;
    std::atomic_size_t tasks_pending_launch;
    std::atomic_size_t tasks_running;
    std::atomic_size_t tasks_suspended;
#else
    _Atomic monad_async_task current_task;
    atomic_size_t tasks_pending_launch;
    atomic_size_t tasks_running;
    atomic_size_t tasks_suspended;
#endif
} *monad_async_executor;

//! \brief Attributes by which to construct an executor
struct monad_async_executor_attr
{
    struct
    {
        //! \brief If this is zero, this executor will be incapable of doing
        //! i/o! It also no longer initialises io_uring for this executor.
        unsigned entries;
        struct io_uring_params params;
    } io_uring_ring, io_uring_wr_ring;
};

/*! \brief EXPENSIVE Creates an executor instance. You must create it on the
 kernel thread where it will be used.

Generally, one also needs to create context switcher instances for each
executor instance. This is because the context switcher needs to store how
to resume the executor when a task's execution suspends.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_create(
    monad_async_executor *ex, struct monad_async_executor_attr *attr);

//! \brief EXPENSIVE Destroys an executor instance.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_executor_destroy(monad_async_executor ex);

//! \brief Processes no more than `max_items` work items, returning the number
//! of items processed which will be at least one. A null `timeout` means wait
//! forever, and a zero timeout will poll without blocking.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_run(
    monad_async_executor ex, size_t max_items, struct timespec *timeout);

//! \brief THREADSAFE Causes a sleeping executor to wake. Can be called from any
//! kernel thread.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_executor_wake(monad_async_executor ex);

#ifdef __cplusplus
}
#endif
