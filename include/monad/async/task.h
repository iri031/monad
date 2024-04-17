#pragma once

#include "context_switcher.h"

#include <stdatomic.h>
#include <stdbool.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C"
{
#endif
typedef struct monad_async_executor_head *monad_async_executor;

//! \brief The public attributes of a task
typedef struct monad_async_task_head
{
    // These can be set by the user
    struct
    {
        monad_async_priority cpu;
        monad_async_priority io;
    } priority;

    monad_async_result result;
    monad_async_result (*user_code)(struct monad_async_task_head *);
    void *user_ptr;

    // The following are not user modifiable
#ifdef __cplusplus
    std::atomic<monad_async_executor> current_executor;
    std::
#else
    _Atomic monad_async_executor current_executor;
#endif
        atomic_bool is_awaiting_dispatch,
        is_pending_launch, is_running, is_suspended_awaiting,
        is_suspended_completed;
    monad_async_priority pending_launch_queue_;
    monad_async_cpu_ticks_count_t ticks_when_attached;
    monad_async_cpu_ticks_count_t ticks_when_detached;
    monad_async_cpu_ticks_count_t ticks_when_suspended_awaiting;
    monad_async_cpu_ticks_count_t ticks_when_suspended_completed;
    monad_async_cpu_ticks_count_t ticks_when_resumed;
    monad_async_cpu_ticks_count_t total_ticks_executed;
} *monad_async_task;

//! \brief Attributes by which to construct a task
struct monad_async_task_attr
{
    //! \brief 0 chooses platform default stack size
    size_t stack_size;
};

//! \brief EXPENSIVE Creates a task instance using the specified context
//! switcher.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_create(
    monad_async_task *task, monad_async_context_switcher switcher,
    struct monad_async_task_attr *attr);

//! \brief EXPENSIVE Destroys a task instance. If the task is currently
//! suspended, it will be cancelled first in which case `EAGAIN` may be returned
//! from this function until cancellation succeeds.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_destroy(monad_async_task task);

//! \brief THREADSAFE Attaches a task instance onto a given executor, which
//! means it will launch the next time the executor runs. If the task is
//! attached already to a different executor, you MUST call this function from
//! that executor's kernel thread. If you optionally choose to reparent the
//! task's context to a new context switcher instance (typical if attaching
//! to an executor on a different kernel thread), it MUST be the same type of
//! context switcher.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_attach(
    monad_async_executor executor, monad_async_task task,
    monad_async_context_switcher
        opt_reparent_switcher); // implemented in executor.c

//! \brief If a task is currently suspended on an operation, cancel it. This can
//! take some time for the relevant io_uring operation to also cancel. If the
//! task is yet to launch, don't launch it. If the task isn't currently running,
//! returns `ENOENT`. The suspension point will return `ECANCELED` next time the
//! task resumes.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_cancel(
    monad_async_executor executor,
    monad_async_task task); // implemented in executor.c

//! \brief Suspend execution of a task for a given duration, which can be zero
//! (which equates "yield").
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_suspend_for_duration(
    monad_async_task task, uint64_t ns); // implemented in executor.c

#ifdef __cplusplus
}
#endif
