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
    monad_async_cpu_ticks_count_t total_ticks_in_run;
    monad_async_cpu_ticks_count_t total_ticks_in_task_launch;
    monad_async_cpu_ticks_count_t total_ticks_in_io_uring;
    monad_async_cpu_ticks_count_t total_ticks_sleeping;
    monad_async_cpu_ticks_count_t total_ticks_in_task_completion;
} *monad_async_executor;

//! \brief Returns true if an executor has work before it
static inline bool monad_async_executor_has_work(monad_async_executor ex)
{
#ifdef __cplusplus
    return ex->current_task.load(std::memory_order_acquire) != nullptr ||
           ex->tasks_pending_launch.load(std::memory_order_acquire) > 0 ||
           ex->tasks_running.load(std::memory_order_acquire) > 0 ||
           ex->tasks_suspended.load(std::memory_order_acquire) > 0;
#else
    return atomic_load_explicit(&ex->current_task, memory_order_acquire) !=
               NULL ||
           atomic_load_explicit(
               &ex->tasks_pending_launch, memory_order_acquire) > 0 ||
           atomic_load_explicit(&ex->tasks_running, memory_order_acquire) > 0 ||
           atomic_load_explicit(&ex->tasks_suspended, memory_order_acquire) > 0;
#endif
}

//! \brief Attributes by which to construct an executor
struct monad_async_executor_attr
{
    struct
    {
        //! \brief If this is zero, this executor will be incapable of doing
        //! i/o! It also no longer initialises io_uring for this executor.
        unsigned entries;
        struct io_uring_params params;

        struct
        {
            //! \brief How many small and large buffers to register.
            unsigned small, large;
        } registered_buffers;
    } io_uring_ring, io_uring_wr_ring;
};

//! \brief A registered i/o buffer
typedef struct monad_async_executor_registered_io_buffer
{
    int index;
    struct iovec iov[1];
} monad_async_executor_registered_io_buffer;

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
//! kernel thread. `cause_run_to_return` causes `monad_async_executor_run()` to
//! return the result given, otherwise the internal sleep wakes, executor state
//! is examined for new work and the sleep reestablished.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_wake(
    monad_async_executor ex, monad_async_result const *cause_run_to_return);

/*! \brief Claim an unused registered buffer, if there is one.

There are two sizes of registered i/o buffer, small and large which are the page
size of the host platform (e.g. 4Kb and 2Mb if on Intel x64). Through being a
single page size, DMA using registered i/o buffers has the lowest possible
overhead.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_executor_claim_registered_io_buffer(
    monad_async_executor_registered_io_buffer *buffer, monad_async_executor ex,
    size_t bytes_requested, bool is_for_write);

//! \brief Release a previously claimed registered buffer.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_executor_release_registered_io_buffer(
    monad_async_executor ex, int buffer_index);

#ifdef __cplusplus
}
#endif
