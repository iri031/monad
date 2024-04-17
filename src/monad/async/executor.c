#define _GNU_SOURCE // to get ppoll

#include "monad/async/executor.h"

#include "monad/async/task.h"

// #define MONAD_ASYNC_EXECUTOR_PRINTING 1

#include "executor_impl.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#include <linux/ioprio.h>
#include <poll.h>

monad_async_result monad_async_executor_create(
    monad_async_executor *ex, struct monad_async_executor_attr *attr)
{
    struct monad_async_executor_impl *p =
        (struct monad_async_executor_impl *)calloc(
            1, sizeof(struct monad_async_executor_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    MONAD_ASYNC_TRY_RESULT(
        (void)monad_async_executor_destroy((monad_async_executor)p),
        monad_async_executor_create_impl(p, attr));
    *ex = (monad_async_executor)p;
    return monad_async_make_success(0);
}

monad_async_result monad_async_executor_destroy(monad_async_executor ex_)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    MONAD_ASYNC_TRY_RESULT(, monad_async_executor_destroy_impl(ex));
    free(ex);
    return monad_async_make_success(0);
}

struct launch_pending_tasks_state
{
    struct monad_async_executor_impl *ex;
    size_t const *max_items;

    size_t items;
    LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
    size_t tasks_pending_launch_count;
    monad_async_priority current_priority;
};

static inline monad_async_result monad_async_executor_impl_launch_pending_tasks(
    void *user_ptr, monad_async_context fake_current_context)
{
    struct launch_pending_tasks_state *state =
        (struct launch_pending_tasks_state *)user_ptr;
    for (; state->current_priority < monad_async_priority_max;
         state->current_priority++) {
        while (state->tasks_pending_launch[state->current_priority].count > 0) {
            if (++state->items > *state->max_items) {
                goto exit;
            }
            struct monad_async_task_impl *task =
                state->tasks_pending_launch[state->current_priority].front;
            LIST_REMOVE(
                state->tasks_pending_launch[state->current_priority],
                task,
                (size_t *)nullptr);
            LIST_APPEND_ATOMIC_COUNTER(
                state->ex->tasks_running[task->head.priority.cpu],
                task,
                &state->ex->head.tasks_running);
            atomic_store_explicit(
                &task->head.is_running, true, memory_order_release);
            atomic_store_explicit(
                &task->head.is_pending_launch, false, memory_order_release);
            task->head.ticks_when_resumed =
                get_ticks_count(memory_order_relaxed);
            atomic_store_explicit(
                &state->ex->head.current_task,
                &task->head,
                memory_order_release);
            // This may suspend, in which case we shall either resume above
            // or it wil return (depends on context switch implementation)
            task->context->switcher->resume(
                fake_current_context, task->context);
        }
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has launched %zu pending tasks\n",
        state->ex,
        state->items);
#endif
    return monad_async_make_success(0);
}

struct resume_tasks_state
{
    struct monad_async_executor_impl *ex;
    size_t const *max_items;

    size_t items;
    monad_async_priority current_priority;
};

static inline monad_async_result monad_async_executor_impl_resume_tasks(
    void *user_ptr, monad_async_context fake_current_context)
{
    struct resume_tasks_state *state = (struct resume_tasks_state *)user_ptr;
    for (; state->current_priority < monad_async_priority_max;
         state->current_priority++) {
        while (state->ex->tasks_suspended_completed[state->current_priority]
                   .count > 0) {
            if (++state->items > *state->max_items) {
                goto exit;
            }
            // Resume execution of the task. If it suspends on
            // another operation, or exits, the loop will resume
            // iterating above or return here
            struct monad_async_task_impl *task =
                state->ex->tasks_suspended_completed[state->current_priority]
                    .front;
            task->context->switcher->resume(
                fake_current_context, task->context);
        }
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has notified %zu tasks of i/o completion "
        "by resumption\n",
        state->ex,
        state->items);
    fflush(stdout);
#endif
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_run_impl(
    struct monad_async_executor_impl *ex, size_t max_items,
    struct timespec *timeout)
{
    struct launch_pending_tasks_state launch_pending_tasks_state = {
        .ex = ex, .max_items = &max_items};
    bool timed_out = false;
    bool retry_after_this = false;
    do {
        timed_out = false;
        retry_after_this = false;
        if (atomic_load_explicit(
                &ex->need_to_empty_eventfd, memory_order_acquire) ||
            atomic_load_explicit(
                &ex->head.tasks_pending_launch, memory_order_acquire) > 0) {
            atomic_lock(&ex->lock);
            for (bool done = false; !done;) {
                done = true;
                for (int n = 0; n < monad_async_priority_max; n++) {
                    if (ex->tasks_pending_launch[n].count > 0) {
                        struct monad_async_task_impl *const task =
                            ex->tasks_pending_launch[n].front;
                        assert(task->head.pending_launch_queue_ == n);
                        LIST_REMOVE_ATOMIC_COUNTER(
                            ex->tasks_pending_launch[n],
                            task,
                            &ex->head.tasks_pending_launch);
                        LIST_APPEND(
                            launch_pending_tasks_state
                                .tasks_pending_launch[task->head.priority.cpu],
                            task,
                            &launch_pending_tasks_state
                                 .tasks_pending_launch_count);
                        done = false;
                    }
                }
            }
            if (atomic_load_explicit(
                    &ex->need_to_empty_eventfd, memory_order_acquire)) {
                eventfd_t v;
                if (-1 == eventfd_read(ex->eventfd, &v)) {
                    atomic_unlock(&ex->lock);
                    return monad_async_make_failure(errno);
                }
                atomic_store_explicit(
                    &ex->need_to_empty_eventfd, false, memory_order_release);
            }
            atomic_unlock(&ex->lock);
        }
        struct timespec no_waiting = {.tv_sec = 0, .tv_nsec = 0};
        if (ex->head.tasks_suspended > 0) {
            for (int n = 0; max_items > 0 && n < monad_async_priority_max;
                 n++) {
                if (ex->tasks_suspended_completed[n].count > 0) {
                    timeout = &no_waiting;
                    break;
                }
            }
        }
        if (launch_pending_tasks_state.tasks_pending_launch_count > 0) {
            timeout = &no_waiting;
            for (int n = 0; max_items > 0 && n < monad_async_priority_max;
                 n++) {
                while (
                    max_items > 0 &&
                    launch_pending_tasks_state.tasks_pending_launch[n].count >
                        0) {
                    struct monad_async_task_impl *task =
                        launch_pending_tasks_state.tasks_pending_launch[n]
                            .front;
                    MONAD_ASYNC_TRY_RESULT(
                        ,
                        task->context->switcher->resume_many(
                            task->context->switcher,
                            monad_async_executor_impl_launch_pending_tasks,
                            &launch_pending_tasks_state));
                    if (launch_pending_tasks_state.items >= max_items) {
                        max_items = 0;
                        break;
                    }
                    else {
                        max_items -= launch_pending_tasks_state.items;
                    }
                }
            }
        }

        if (ex->ring.ring_fd != 0) {
            // Submit all enqueued ops, and wait for some completions
            struct io_uring_cqe *cqe = nullptr;
            int r = io_uring_peek_cqe(&ex->ring, &cqe);
            if (0 != r) {
                if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                    printf(
                        "*** Executor %p submits and waits forever due to "
                        "infinite "
                        "timeout\n",
                        ex);
#endif
                    r = io_uring_submit_and_wait(&ex->ring, 1);
                    if (r < 0) {
                        return monad_async_make_failure(-r);
                    }
                    r = io_uring_peek_cqe(&ex->ring, &cqe);
                }
                else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                    printf(
                        "*** Executor %p submits and does not wait due to zero "
                        "timeout\n",
                        ex);
#endif
                    r = io_uring_submit(&ex->ring);
                    if (r < 0) {
                        return monad_async_make_failure(-r);
                    }
                    r = io_uring_peek_cqe(&ex->ring, &cqe);
                }
                else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                    printf(
                        "*** Executor %p submits and waits for a non-infinite "
                        "timeout "
                        "%ld-%ld\n",
                        ex,
                        timeout->tv_sec,
                        timeout->tv_nsec);
#endif
                    if (ex->ring.features & IORING_FEAT_EXT_ARG) {
                        r = io_uring_submit(&ex->ring);
                        if (r < 0) {
                            return monad_async_make_failure(-r);
                        }
                    }
                    r = io_uring_wait_cqe_timeout(
                        &ex->ring, &cqe, (struct __kernel_timespec *)timeout);
                }
            }
            if (r < 0) {
                if (r == -ETIME) {
                    timed_out = true;
                }
                else if (r == -EAGAIN) {
                    // temporary failure, ignore it
                }
                else {
                    return monad_async_make_failure(-r);
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf("*** Executor %p sees cqe=%p from io_uring wait\n", ex, cqe);
#endif
            // Always empty the completions queue irrespective of max_items
            unsigned head;
            unsigned i = 0;
            io_uring_for_each_cqe(&ex->ring, head, cqe)
            {
                i++;
                if (io_uring_cqe_get_data(cqe) ==
                    EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC) {
                    retry_after_this = true;
                }
                else {
                    struct monad_async_task_impl *task =
                        (struct monad_async_task_impl *)io_uring_cqe_get_data(
                            cqe);
                    task->head.ticks_when_suspended_completed =
                        get_ticks_count(memory_order_relaxed);
                    if (task->please_cancel_invoked) {
                        task->head.result = monad_async_make_failure(ECANCELED);
                    }
                    else if (cqe->res < 0) {
                        task->head.result = monad_async_make_failure(-cqe->res);
                    }
                    else {
                        task->head.result = monad_async_make_success(cqe->res);
                    }
                    assert(atomic_load_explicit(
                        &task->head.is_suspended_awaiting,
                        memory_order_acquire));
                    atomic_store_explicit(
                        &task->head.is_suspended_awaiting,
                        false,
                        memory_order_release);
                    LIST_REMOVE(
                        ex->tasks_suspended_awaiting[task->head.priority.cpu],
                        task,
                        (size_t *)nullptr);
                    atomic_store_explicit(
                        &task->head.is_suspended_completed,
                        true,
                        memory_order_release);
                    LIST_APPEND(
                        ex->tasks_suspended_completed[task->head.priority.cpu],
                        task,
                        (size_t *)nullptr);
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Executor %p has dequeued %zu completions from io_uring\n",
                ex,
                i);
#endif
            io_uring_cq_advance(&ex->ring, i);
        }
        else {
            // If io_uring was not enabled for this executor, use the eventfd as
            // the synchronisation object
            if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p waits forever due to infinite "
                    "timeout\n",
                    ex);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                int r = ppoll(fds, 1, nullptr, nullptr);
                if (r == 0) {
                    timed_out = true;
                }
                else if (r == -1) {
                    return monad_async_make_failure(errno);
                }
                else {
                    retry_after_this = true;
                }
            }
            else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p does not wait due to zero "
                    "timeout\n",
                    ex);
#endif
            }
            else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p waits for a non-infinite "
                    "timeout "
                    "%ld-%ld\n",
                    ex,
                    timeout->tv_sec,
                    timeout->tv_nsec);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                int r = ppoll(fds, 1, timeout, nullptr);
                if (r == 0) {
                    timed_out = true;
                }
                else if (r == -1) {
                    return monad_async_make_failure(errno);
                }
                else {
                    retry_after_this = true;
                }
            }
        }
        struct resume_tasks_state resume_tasks_state = {
            .ex = ex, .max_items = &max_items};
        if (max_items > 0) {
            for (;
                 resume_tasks_state.current_priority < monad_async_priority_max;
                 resume_tasks_state.current_priority++) {
                if (ex->tasks_suspended_completed[resume_tasks_state
                                                      .current_priority]
                        .count > 0) {
                    struct monad_async_task_impl *task =
                        ex->tasks_suspended_completed[resume_tasks_state
                                                          .current_priority]
                            .front;
                    MONAD_ASYNC_TRY_RESULT(
                        ,
                        task->context->switcher->resume_many(
                            task->context->switcher,
                            monad_async_executor_impl_resume_tasks,
                            &resume_tasks_state));
                    break;
                }
            }
        }
        size_t items_processed =
            launch_pending_tasks_state.items + resume_tasks_state.items;
        if (items_processed > 0) {
            return monad_async_make_success((intptr_t)items_processed);
        }
    }
    while (retry_after_this);
    return timed_out ? monad_async_make_failure(ETIME)
                     : monad_async_make_success(0);
}

monad_async_result monad_async_executor_run(
    monad_async_executor ex_, size_t max_items, struct timespec *timeout)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
#ifndef NDEBUG
    if (!thrd_equal(thrd_current(), ex->owning_thread)) {
        fprintf(
            stderr,
            "FATAL: You must run an executor from the same kernel "
            "thread on "
            "which it was created.\n");
        abort();
    }
#endif
    if (ex->within_run) {
        fprintf(
            stderr,
            "FATAL: You must never run an executor which is already "
            "running "
            "(i.e. recursing into the executor is forbidden).\n");
        abort();
    }
    ex->within_run = true;
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p enters run\n", ex);
#endif
    monad_async_result ret =
        monad_async_executor_run_impl(ex, max_items, timeout);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p exits run having processed %zu items\n",
        ex,
        ret.value);
#endif
    ex->within_run = false;
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    return ret;
}

static monad_async_result monad_async_executor_suspend_impl(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    monad_async_result (*please_cancel)(struct monad_async_task_impl *task))
{
    assert(atomic_load_explicit(&task->head.is_running, memory_order_acquire));
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        &task->head);
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    task->please_cancel = please_cancel;
    atomic_store_explicit(&task->head.is_running, false, memory_order_release);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_running[task->head.priority.cpu],
        task,
        &ex->head.tasks_running);
    atomic_store_explicit(
        &task->head.is_suspended_awaiting, true, memory_order_release);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_suspended_awaiting[task->head.priority.cpu],
        task,
        &ex->head.tasks_suspended);
    task->head.ticks_when_suspended_awaiting =
        get_ticks_count(memory_order_relaxed);
    task->head.total_ticks_executed +=
        task->head.ticks_when_suspended_awaiting -
        task->head.ticks_when_resumed;
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p suspends task %p\n", ex, task);
#endif
    task->context->switcher->suspend_and_call_resume(task->context, nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p resumes task %p\n", ex, task);
#endif
    task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
    assert(!atomic_load_explicit(
        &task->head.is_suspended_awaiting, memory_order_acquire));
    assert(atomic_load_explicit(
        &task->head.is_suspended_completed, memory_order_acquire));
    atomic_store_explicit(
        &task->head.is_suspended_completed, false, memory_order_release);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_suspended_completed[task->head.priority.cpu],
        task,
        &ex->head.tasks_suspended);
    atomic_store_explicit(&task->head.is_running, true, memory_order_release);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_running[task->head.priority.cpu],
        task,
        &ex->head.tasks_running);
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        nullptr);
    atomic_store_explicit(
        &ex->head.current_task, &task->head, memory_order_release);
    task->please_cancel_invoked = false;
    task->please_cancel = nullptr;
    return task->head.result;
}

monad_async_result monad_async_executor_wake(monad_async_executor ex_)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    atomic_store_explicit(
        &ex->need_to_empty_eventfd, true, memory_order_release);
    if (-1 == eventfd_write(ex->eventfd, 1)) {
        return monad_async_make_success(errno);
    }
    return monad_async_make_success(0);
}

void monad_async_executor_task_exited(monad_async_task task_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    assert(atomic_load_explicit(&task_->is_running, memory_order_acquire));
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        task_);
    atomic_lock(&ex->lock);
    LIST_REMOVE_ATOMIC_COUNTER(
        ex->tasks_running[task->head.priority.cpu],
        task,
        &ex->head.tasks_running);
    atomic_unlock(&ex->lock);
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    task_->ticks_when_detached = get_ticks_count(memory_order_relaxed);
    task_->total_ticks_executed +=
        task_->ticks_when_detached - task_->ticks_when_resumed;
    atomic_store_explicit(&task_->is_running, false, memory_order_release);
    atomic_store_explicit(
        &task_->current_executor, nullptr, memory_order_release);
}

monad_async_result monad_async_task_attach(
    monad_async_executor ex_, monad_async_task task_,
    monad_async_context_switcher opt_reparent_switcher)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->head.user_code == nullptr) {
        return monad_async_make_failure(EINVAL);
    }
    bool const on_foreign_thread =
        !thrd_equal(thrd_current(), ex->owning_thread);
    if (atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire) != nullptr) {
#ifndef NDEBUG
        if (on_foreign_thread) {
            fprintf(
                stderr,
                "FATAL: You must detach a task on the same kernel "
                "thread on "
                "which its executor is run.\n");
            abort();
        }
#endif
        atomic_lock(&ex->lock);

        if (atomic_load_explicit(
                &task->head.is_pending_launch, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_pending_launch[task->head.pending_launch_queue_],
                task,
                &ex->head.tasks_pending_launch);
            atomic_store_explicit(
                &task->head.is_pending_launch, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_running, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_running[task->head.priority.cpu],
                task,
                &ex->head.tasks_running);
            atomic_store_explicit(
                &task->head.is_running, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_awaiting, memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_awaiting[task->head.priority.cpu],
                task,
                &ex->head.tasks_suspended);
            atomic_store_explicit(
                &task->head.is_suspended_awaiting, false, memory_order_release);
        }
        else if (atomic_load_explicit(
                     &task->head.is_suspended_completed,
                     memory_order_acquire)) {
            LIST_REMOVE_ATOMIC_COUNTER(
                ex->tasks_suspended_completed[task->head.priority.cpu],
                task,
                &ex->head.tasks_suspended);
            atomic_store_explicit(
                &task->head.is_suspended_completed,
                false,
                memory_order_release);
        }
        atomic_unlock(&ex->lock);
    }
    if (opt_reparent_switcher) {
        if (opt_reparent_switcher->create != task->context->switcher->create) {
            fprintf(
                stderr,
                "FATAL: If reparenting context switcher, the new parent must "
                "be the same type of context switcher.\n");
            abort();
        }
        task->context->switcher->contexts--;
        task->context->switcher = opt_reparent_switcher;
        task->context->switcher->contexts++;
    }
    atomic_store_explicit(
        &task->head.current_executor,
        (monad_async_executor)ex,
        memory_order_release);
    atomic_store_explicit(
        &task->head.is_pending_launch, true, memory_order_release);
    task->head.ticks_when_attached = get_ticks_count(memory_order_relaxed);
    task->head.ticks_when_detached = 0;
    task->head.ticks_when_resumed = 0;
    task->head.ticks_when_suspended_awaiting = 0;
    task->head.ticks_when_suspended_completed = 0;
    task->head.total_ticks_executed = 0;
    atomic_lock(&ex->lock);
    LIST_APPEND_ATOMIC_COUNTER(
        ex->tasks_pending_launch[ex->tasks_pending_launch_next_queue],
        task,
        &ex->head.tasks_pending_launch);
    task->head.pending_launch_queue_ = ex->tasks_pending_launch_next_queue;
    if (++ex->tasks_pending_launch_next_queue == monad_async_priority_max) {
        ex->tasks_pending_launch_next_queue = monad_async_priority_high;
    }
    if (on_foreign_thread) {
        MONAD_ASYNC_TRY_RESULT(
            (void)atomic_unlock(&ex->lock),
            monad_async_executor_wake(&ex->head));
    }
    atomic_unlock(&ex->lock);
    return monad_async_make_success(0);
}

monad_async_result
monad_async_task_cancel(monad_async_executor ex_, monad_async_task task_)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire) == nullptr) {
        return monad_async_make_failure(ENOENT);
    }
    if (atomic_load_explicit(
            &task->head.is_pending_launch, memory_order_acquire)) {
        atomic_lock(&ex->lock);
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_pending_launch[task->head.pending_launch_queue_],
            task,
            &ex->head.tasks_pending_launch);
        atomic_store_explicit(
            &task->head.is_pending_launch, false, memory_order_release);
        atomic_unlock(&ex->lock);
        return monad_async_make_success(0);
    }
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        fprintf(
            stderr, "TODO: Switch context back to root, and end the task\n");
        abort();
    }
    if (atomic_load_explicit(
            &task->head.is_suspended_awaiting, memory_order_acquire)) {
        atomic_lock(&ex->lock);
        task->please_cancel_invoked = true;
        // Invoke the cancellation routine
        if (task->please_cancel == nullptr) {
            atomic_unlock(&ex->lock);
            return monad_async_make_failure(EAGAIN);
        }
        monad_async_result r = task->please_cancel(task);
        atomic_unlock(&ex->lock);
        return r;
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        atomic_lock(&ex->lock);
        // Have this return ECANCELED when it resumes
        task->head.result = monad_async_make_failure(ECANCELED);
        atomic_unlock(&ex->lock);
    }
    else {
        return monad_async_make_failure(ENOENT);
    }
    return monad_async_make_success(0);
}

static inline monad_async_result
monad_async_task_suspend_for_duration_cancel(struct monad_async_task_impl *task)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->ring);
    if (sqe == nullptr) {
        fprintf(
            stderr,
            "TODO: Handle SQE exhaustation via suspend until free SQE "
            "entries "
            "appear.\n");
        abort();
    }
    io_uring_prep_timeout_remove(sqe, (__u64)task, 0);
    return monad_async_make_success(EAGAIN); // Canceller needs to wait
}

monad_async_result
monad_async_task_suspend_for_duration(monad_async_task task_, uint64_t ns)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr ||
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) !=
            task_) {
        fprintf(
            stderr,
            "FATAL: Task execution suspension invoked not by the "
            "current task "
            "executing.\n");
        abort();
    }
    assert(ex->within_run == true);
    struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->ring);
    if (sqe == nullptr) {
        fprintf(
            stderr,
            "TODO: Handle SQE exhaustation via suspend until free SQE "
            "entries "
            "appear.\n");
        abort();
    }
    // timespec must live until resumption
    struct __kernel_timespec ts;
    if (ns == 0) {
        io_uring_prep_nop(sqe);
    }
    else {
        ts.tv_sec = (long long)(ns / 1000000000);
        ts.tv_nsec = (long long)(ns % 1000000000);
        io_uring_prep_timeout(sqe, &ts, (unsigned)-1, 0);
    }

    switch (task_->priority.io) {
    default:
        break;
    case monad_async_priority_high:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case monad_async_priority_low:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    }

    io_uring_sqe_set_data(sqe, task);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "suspend_for_duration\n",
        task,
        ex);
#endif
    monad_async_result ret = monad_async_executor_suspend_impl(
        ex, task, monad_async_task_suspend_for_duration_cancel);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "suspend_for_duration\n",
        task,
        ex);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        if (ret.error.value == ETIME && ns > 0) {
            // io_uring returns timeouts as failure with ETIME, so
            // filter those out
            return monad_async_make_success(0);
        }
        return ret;
    }
    return monad_async_make_success(0);
}
