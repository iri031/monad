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

typedef struct monad_async_task_head *monad_async_task;

struct monad_fiber_task;
struct monad_fiber_scheduler;

//! \brief An i/o status state used to identify an i/o in progress. Must NOT
//! move in memory until the operation completes.
typedef struct monad_async_io_status
{
    struct monad_async_io_status *prev, *next;
    monad_async_result (*cancel_)(
        monad_async_task, struct monad_async_io_status *);

    //! Unspecified value immediately after initiating call returns. Will become
    //! bytes transferred if operation is successful, or another error if it
    //! fails or is cancelled.
    monad_async_result result;

    monad_async_cpu_ticks_count_t ticks_when_initiated;
    monad_async_cpu_ticks_count_t ticks_when_completed;
    monad_async_cpu_ticks_count_t ticks_when_reaped;

    // You can place any additional data you want after here ...
} monad_async_io_status;

//! \brief True if the i/o is currently in progress
static inline bool
monad_async_is_io_in_progress(monad_async_io_status const *iostatus)
{
    return iostatus->result.flags == (unsigned)-1;
}

//! \brief Number of the i/o is currently in progress
static inline size_t
monad_async_io_in_progress(monad_async_io_status const *iostatus, size_t len)
{
    size_t ret = 0;
    for (size_t n = 0; n < len; n++) {
        if (monad_async_is_io_in_progress(&iostatus[n])) {
            ret++;
        }
    }
    return ret;
}

//! \brief The public attributes of a task
struct monad_async_task_head
{
    // These can be set by the user
    monad_async_result (*user_code)(struct monad_async_task_head *);
    void *user_ptr;

    // The following are not user modifiable
    struct
    {
        monad_async_priority cpu;
        monad_async_priority io;
    } priority;

    monad_async_result result;
    // All of these next refer to the i/o executor only i.e. if running on a
    // foreign executor, is_running will be false as that is not the i/o
    // executor.
#ifdef __cplusplus
    std::atomic<monad_async_executor> current_executor;
    std::
#else
    _Atomic monad_async_executor current_executor;
#endif
        atomic_bool is_awaiting_dispatch,
        is_pending_launch, is_running, is_suspended_sqe_exhaustion,
        is_suspended_sqe_exhaustion_wr, is_suspended_awaiting,
        is_suspended_completed, is_running_on_foreign_executor;

    monad_async_priority pending_launch_queue_;

    monad_async_cpu_ticks_count_t ticks_when_submitted;
    monad_async_cpu_ticks_count_t ticks_when_attached;
    monad_async_cpu_ticks_count_t ticks_when_detached;
    monad_async_cpu_ticks_count_t ticks_when_suspended_awaiting;
    monad_async_cpu_ticks_count_t ticks_when_suspended_completed;
    monad_async_cpu_ticks_count_t ticks_when_resumed;
    monad_async_cpu_ticks_count_t total_ticks_executed;

    size_t io_submitted, io_completed_not_reaped;
};

//! \brief True if the task has completed executing and has exited
static inline bool monad_async_task_has_exited(monad_async_task const task)
{
#ifdef __cplusplus
    return task->is_awaiting_dispatch.load(std::memory_order_acquire) ==
               false &&
           task->current_executor.load(std::memory_order_acquire) == nullptr &&
           task->is_running_on_foreign_executor.load(
               std::memory_order_acquire) == false;
#else
    return atomic_load_explicit(
               &task->is_awaiting_dispatch, memory_order_acquire) == false &&
           atomic_load_explicit(
               &task->current_executor, memory_order_acquire) == NULL &&
           atomic_load_explicit(
               &task->is_running_on_foreign_executor, memory_order_acquire);
#endif
}

//! \brief If the i/o is currently in progress, returns the task which initiated
//! the i/o. Otherwise returns nullptr.
static inline monad_async_task
monad_async_io_status_owning_task(monad_async_io_status const *iostatus)
{
    if (!monad_async_is_io_in_progress(iostatus)) {
        return NULL;
    }

    union punner
    {
        monad_async_result res;
        monad_async_task task;
    } pun;

    pun.res = iostatus->result;
    return pun.task;
}

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

//! \brief THREADSAFE If a task is currently suspended on an operation, cancel
//! it. This can take some time for the relevant io_uring operation to also
//! cancel. If the task is yet to launch, don't launch it. If the task isn't
//! currently running, returns `ENOENT`. The suspension point will return
//! `ECANCELED` next time the task resumes.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_cancel(
    monad_async_executor executor,
    monad_async_task task); // implemented in executor.c

//! \brief Change the CPU or i/o priority of a task
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_set_priorities(
    monad_async_task task, monad_async_priority cpu,
    monad_async_priority io); // implemented in executor.c

//! \brief Ask io_uring to cancel a previously initiated operation. It can take
//! some time for io_uring to cancel an operation, and it may ignore your
//! request.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_io_cancel(
    monad_async_task task,
    monad_async_io_status *iostatus); // implemented in executor.c

//! \brief Iterate through completed i/o for this task, reaping each from the
//! completed but not repeated list.
MONAD_ASYNC_NODISCARD extern monad_async_io_status *
monad_async_task_completed_io(
    monad_async_task task); // implemented in executor.c

//! \brief CANCELLATION POINT Suspend execution of a task for a given duration,
//! which can be zero (which equates "yield"). If `completed` is not null, if
//! any i/o which the task has initiated completes during the suspension, resume
//! the task setting `completed` to which i/o has just completed.
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_suspend_for_duration(
    monad_async_io_status **completed, monad_async_task task,
    uint64_t ns); // implemented in executor.c

//! \brief CANCELLATION POINT Combines `monad_async_task_completed_io()` and
//! `monad_async_task_suspend_for_duration()` to conveniently reap completed
//! i/o, suspending the task until more i/o completes. Returns zero when no more
//! i/o, otherwise returns i/o completed not reaped including i/o
//! returned.
static inline monad_async_result monad_async_task_suspend_until_completed_io(
    monad_async_io_status **completed, monad_async_task task, uint64_t ns)
{
    *completed = monad_async_task_completed_io(task);
    if (*completed != NULL) {
        return monad_async_make_success(
            1 + (intptr_t)task->io_completed_not_reaped);
    }
    if (task->io_submitted == 0) {
        return monad_async_make_success(0);
    }
    monad_async_result r =
        monad_async_task_suspend_for_duration(completed, task, ns);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
        return r;
    }
    *completed = monad_async_task_completed_io(task);
    return monad_async_make_success(
        1 + (intptr_t)task->io_completed_not_reaped);
}

/***************************************************************************/

/*! \brief Retrieve the `monad_fiber_task` structure for the async task, from
which later on its original `monad_async_task` can be retrieved.

The `resume` member is set to resume the context, invoking the task's
`user_code` as if the task were attached to an i/o executor (but the task is NOT
attached to the i/o executor, as it is executing on a compute executor). After
`resume` is invoked, `is_running_on_foreign_executor` will be true up until/if
the task is attached to an i/o executor, or it returns to the compute executor.

The `destroy` member is set to null and will need to be filled in by calling
code. It is suggested that if the task is currently attached to an i/o executor
(`current_executor` is not null), `monad_async_task_cancel()` is used to attempt
a cancellation of any pending i/o.

*/
extern struct monad_fiber_task *
monad_fiber_task_from_async_task(monad_async_task task);

//! \brief Retrieve the original `monad_async_task` from a fiber task structure
//! previously returned by `monad_fiber_task_from_async_task`.
extern monad_async_task
monad_async_task_from_fiber_task(struct monad_fiber_task *task);

/*! \brief THREADSAFE Suspend the calling task and call
`monad_async_task_attach()` to have the context resume execution on the
specified i/o executor.

Control flow will return to the caller of `resume` after this so it can go
execute other compute work. After this `is_running_on_foreign_executor` will
be false.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_fiber_resume_on_io_executor(
    monad_async_executor executor, monad_async_task task,
    monad_async_context_switcher opt_reparent_switcher);

/*! \brief THREADSAFE Suspend the calling task and call
`monad_fiber_scheduler_post()` to have the context resume execution on the
specified computer executor.

After this `is_running_on_foreign_executor` will be true.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_fiber_resume_on_compute_executor(
    struct monad_fiber_scheduler *scheduler, monad_async_task task,
    int64_t priority, monad_async_context_switcher opt_reparent_switcher);

#ifdef __cplusplus
}
#endif
