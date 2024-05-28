#define _GNU_SOURCE // to get ppoll

#include "monad/async/executor.h"

#include "monad/async/task.h"

#include "executor_impl.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

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
            atomic_load_explicit(&task->context->switcher, memory_order_acquire)
                ->resume(fake_current_context, task->context);
        }
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has launched %zu pending tasks\n",
        (void *)state->ex,
        state->items);
#endif
    return monad_async_make_success(0);
}

struct resume_tasks_state
{
    struct monad_async_executor_impl *ex;
    size_t const *global_max_items, local_max_items;
    struct list_define_p_monad_async_task_impl_t *wait_list;

    size_t items;
    monad_async_priority current_priority;
};

static inline monad_async_result monad_async_executor_impl_resume_tasks(
    void *user_ptr, monad_async_context fake_current_context)
{
    struct resume_tasks_state *state = (struct resume_tasks_state *)user_ptr;
    for (; state->current_priority < monad_async_priority_max;
         state->current_priority++) {
        struct list_define_p_monad_async_task_impl_t *wait_list =
            &state->wait_list[state->current_priority];
        while (wait_list->count > 0) {
            if (state->items >= *state->global_max_items ||
                state->items >= state->local_max_items) {
                goto exit;
            }
            ++state->items;
            // Resume execution of the task. If it suspends on
            // another operation, or exits, the loop will resume
            // iterating above or return here
            struct monad_async_task_impl *task = wait_list->front;
            atomic_load_explicit(&task->context->switcher, memory_order_acquire)
                ->resume(fake_current_context, task->context);
        }
    }
exit:
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p has notified %zu tasks of i/o completion "
        "by resumption\n",
        (void *)state->ex,
        state->items);
    fflush(stdout);
#endif
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_run_impl(
    struct monad_async_executor_impl *ex, size_t max_items,
    struct timespec *timeout_)
{
    struct timespec *timeout = timeout_;
    struct launch_pending_tasks_state launch_pending_tasks_state = {
        .ex = ex, .max_items = &max_items};
    bool timed_out = false;
    bool retry_after_this = false;
    do {
        timed_out = false;
        retry_after_this = false;
        monad_async_cpu_ticks_count_t const launch_begin =
            get_ticks_count(memory_order_relaxed);
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
        struct timespec no_waiting = {.tv_sec = 0, .tv_nsec = 0},
                        single_millisecond_waiting = {
                            .tv_sec = 0, .tv_nsec = 1000000};
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
                    monad_async_context_switcher task_switcher =
                        atomic_load_explicit(
                            &task->context->switcher, memory_order_acquire);
                    MONAD_ASYNC_TRY_RESULT(
                        ,
                        task_switcher->resume_many(
                            task_switcher,
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
        monad_async_cpu_ticks_count_t const launch_end =
            get_ticks_count(memory_order_relaxed);
        ex->head.total_ticks_in_task_launch += launch_end - launch_begin;

        if (ex->ring.ring_fd != 0) {
            monad_async_cpu_ticks_count_t const io_uring_begin =
                get_ticks_count(memory_order_relaxed);
            // Submit all enqueued ops, and wait for some completions
            struct io_uring_cqe *cqe = nullptr;
            struct io_uring *ring = nullptr;
            int r = 1;
            if (ex->wr_ring_ops_outstanding > 0) {
                ring = &ex->wr_ring;
                r = io_uring_submit(ring);
                if (r < 0) {
                    return monad_async_make_failure(-r);
                }
                while (max_items > 0 &&
                       atomic_load_explicit(
                           &ex->head.tasks_suspended_sqe_exhaustion,
                           memory_order_acquire) > 0 &&
                       io_uring_sq_space_left(&ex->wr_ring) > 0) {
                    struct resume_tasks_state resume_tasks_state = {
                        .ex = ex,
                        .global_max_items = &max_items,
                        .local_max_items = 1,
                        .wait_list = ex->tasks_suspended_submission_wr_ring};
                    for (; resume_tasks_state.current_priority <
                           monad_async_priority_max;
                         resume_tasks_state.current_priority++) {
                        if (ex->tasks_suspended_submission_wr_ring
                                [resume_tasks_state.current_priority]
                                    .count > 0) {
                            struct io_uring_sqe *sqe =
                                io_uring_get_sqe(&ex->wr_ring);
                            if (sqe == nullptr) {
                                break;
                            }
                            struct monad_async_task_impl *task =
                                ex->tasks_suspended_submission_wr_ring
                                    [resume_tasks_state.current_priority]
                                        .front;
#if MONAD_ASYNC_EXECUTOR_PRINTING
                            printf(
                                "*** Executor %p initiates resumption of "
                                "task %p from write SQE exhaustion. "
                                "sqe=%p. sqes=%u cqes=%u.\n",
                                (void *)ex,
                                (void *)task,
                                (void *)sqe,
                                io_uring_sq_ready(&ex->wr_ring),
                                io_uring_cq_ready(&ex->wr_ring));
                            fflush(stdout);
#endif
                            monad_async_context_switcher task_switcher =
                                atomic_load_explicit(
                                    &task->context->switcher,
                                    memory_order_acquire);
                            MONAD_ASYNC_TRY_RESULT(
                                ,
                                task_switcher->resume_many(
                                    task_switcher,
                                    monad_async_executor_impl_resume_tasks,
                                    &resume_tasks_state));
                            if (resume_tasks_state.items > 0) {
                                max_items--;
                            }
                            break;
                        }
                    }
                }
                r = io_uring_peek_cqe(ring, &cqe);
                if (timeout == nullptr || timeout != &no_waiting ||
                    timespec_to_ns(timeout) > 1000000) {
                    timeout = &single_millisecond_waiting;
                }
                if (0 == r) {
                    ex->wr_ring_ops_outstanding--;
                }
            }
            if (0 != r) {
                ring = &ex->ring;
                r = io_uring_peek_cqe(ring, &cqe);
                if (0 != r) {
                    while (max_items > 0 &&
                           atomic_load_explicit(
                               &ex->head.tasks_suspended_sqe_exhaustion,
                               memory_order_acquire) > 0 &&
                           io_uring_sq_space_left(&ex->ring) > 0) {
                        struct resume_tasks_state resume_tasks_state = {
                            .ex = ex,
                            .global_max_items = &max_items,
                            .local_max_items = 1,
                            .wait_list = ex->tasks_suspended_submission_ring};
                        for (; resume_tasks_state.current_priority <
                               monad_async_priority_max;
                             resume_tasks_state.current_priority++) {
                            if (ex->tasks_suspended_submission_ring
                                    [resume_tasks_state.current_priority]
                                        .count > 0) {
                                struct io_uring_sqe *sqe =
                                    io_uring_get_sqe(&ex->ring);
                                if (sqe == nullptr) {
                                    break;
                                }
                                struct monad_async_task_impl *task =
                                    ex->tasks_suspended_submission_ring
                                        [resume_tasks_state.current_priority]
                                            .front;
#if MONAD_ASYNC_EXECUTOR_PRINTING
                                printf(
                                    "*** Executor %p initiates resumption of "
                                    "task %p from non-write SQE exhaustion. "
                                    "sqe=%p. sqes=%u cqes=%u.\n",
                                    (void *)ex,
                                    (void *)task,
                                    (void *)sqe,
                                    io_uring_sq_ready(&ex->ring),
                                    io_uring_cq_ready(&ex->ring));
                                fflush(stdout);
#endif
                                monad_async_context_switcher task_switcher =
                                    atomic_load_explicit(
                                        &task->context->switcher,
                                        memory_order_acquire);
                                MONAD_ASYNC_TRY_RESULT(
                                    ,
                                    task_switcher->resume_many(
                                        task_switcher,
                                        monad_async_executor_impl_resume_tasks,
                                        &resume_tasks_state));
                                if (resume_tasks_state.items > 0) {
                                    max_items--;
                                }
                                break;
                            }
                        }
                    }
                    if (atomic_load_explicit(
                            &ex->head.tasks_suspended_sqe_exhaustion,
                            memory_order_acquire) > 0) {
                        // SQEs should get consumed quite quickly, so don't
                        // stall unblocking tasks waiting on SQEs
                        timeout = &no_waiting;
                    }
                    if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** Executor %p submits and waits forever due "
                            "to "
                            "infinite timeout. sqes=%u cqes=%u\n",
                            (void *)ex,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));
#endif
                        monad_async_cpu_ticks_count_t const sleep_begin =
                            get_ticks_count(memory_order_relaxed);
                        r = io_uring_submit_and_wait(ring, 1);
                        monad_async_cpu_ticks_count_t const sleep_end =
                            get_ticks_count(memory_order_relaxed);
                        ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
                        if (r < 0) {
                            return monad_async_make_failure(-r);
                        }
                        r = io_uring_peek_cqe(ring, &cqe);
                    }
                    else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** Executor %p submits and does not wait due "
                            "to "
                            "zero "
                            "timeout. sqes=%u cqes=%u\n",
                            (void *)ex,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));

#endif
                        r = io_uring_submit(ring);
                        if (r < 0) {
                            return monad_async_make_failure(-r);
                        }
                        r = io_uring_peek_cqe(ring, &cqe);
                    }
                    else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** Executor %p submits and waits for a "
                            "non-infinite "
                            "timeout %ld-%ld. sqes=%u cqes=%u\n",
                            (void *)ex,
                            timeout->tv_sec,
                            timeout->tv_nsec,
                            io_uring_sq_ready(ring),
                            io_uring_cq_ready(ring));

#endif
                        if (ring->features & IORING_FEAT_EXT_ARG) {
                            r = io_uring_submit(ring);
                            if (r < 0) {
                                return monad_async_make_failure(-r);
                            }
                        }
                        monad_async_cpu_ticks_count_t const sleep_begin =
                            get_ticks_count(memory_order_relaxed);
                        r = io_uring_wait_cqe_timeout(
                            ring, &cqe, (struct __kernel_timespec *)timeout);
                        monad_async_cpu_ticks_count_t const sleep_end =
                            get_ticks_count(memory_order_relaxed);
                        ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
                    }
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
            printf(
                "*** Executor %p sees cqe=%p from io_uring wait. "
                "wr_ring=%d. "
                "sqes=%u "
                "cqes=%u\n",
                (void *)ex,
                (void *)cqe,
                ring == &ex->wr_ring,
                io_uring_sq_ready(ring),
                io_uring_cq_ready(ring));
#endif
            // Always empty the completions queue irrespective of max_items
            unsigned head;
            unsigned i = 0;
            io_uring_for_each_cqe(ring, head, cqe)
            {
                i++;
                struct monad_async_task_impl *task;
                monad_async_io_status *iostatus;
                uintptr_t magic;
                io_uring_cqe_get_data(task, iostatus, magic, cqe);
                if (task != nullptr) {
                resume_task:
                    if (atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire)) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                        printf(
                            "*** %u. Executor %p resumes suspended task "
                            "%p (cpu priority=%d, i/o priority=%d)\n",
                            i,
                            (void *)ex,
                            (void *)task,
                            (int)task->head.priority.cpu,
                            (int)task->head.priority.io);
#endif
                        task->head.ticks_when_suspended_completed =
                            get_ticks_count(memory_order_relaxed);
                        if (task->please_cancel_invoked) {
                            task->head.result =
                                monad_async_make_failure(ECANCELED);
                        }
                        else if (cqe->res < 0) {
                            task->head.result =
                                monad_async_make_failure(-cqe->res);
                        }
                        else {
                            task->head.result =
                                monad_async_make_success(cqe->res);
                        }
                        atomic_store_explicit(
                            &task->head.is_suspended_awaiting,
                            false,
                            memory_order_release);
                        LIST_REMOVE(
                            ex->tasks_suspended_awaiting[task->head.priority
                                                             .cpu],
                            task,
                            (size_t *)nullptr);
                        atomic_store_explicit(
                            &task->head.is_suspended_completed,
                            true,
                            memory_order_release);
                        LIST_APPEND(
                            ex->tasks_suspended_completed[task->head.priority
                                                              .cpu],
                            task,
                            (size_t *)nullptr);
                    }
                }
                else if (iostatus != nullptr) {
                    task = *(struct monad_async_task_impl **)&iostatus->result;
#if MONAD_ASYNC_EXECUTOR_PRINTING
                    printf(
                        "*** %u. Executor %p gets result of i/o %p "
                        "initiated "
                        "by task %p (cpu priority=%d, i/o priority=%d)\n",
                        i,
                        (void *)ex,
                        (void *)iostatus,
                        (void *)task,
                        (int)task->head.priority.cpu,
                        (int)task->head.priority.io);
#endif
                    assert(task != nullptr);
                    LIST_REMOVE(
                        task->io_submitted, iostatus, &task->head.io_submitted);
                    LIST_APPEND(
                        task->io_completed,
                        iostatus,
                        &task->head.io_completed_not_reaped);
                    iostatus->cancel_ = nullptr;
                    iostatus->ticks_when_completed =
                        get_ticks_count(memory_order_relaxed);
                    if (cqe->res < 0) {
                        iostatus->result = monad_async_make_failure(-cqe->res);
                    }
                    else {
                        iostatus->result = monad_async_make_success(cqe->res);
                    }
                    if (task->completed != nullptr &&
                        atomic_load_explicit(
                            &task->head.is_suspended_awaiting,
                            memory_order_acquire)) {
                        *task->completed = iostatus;
                        task->completed = nullptr;
                        cqe->res = (int)task->head.io_completed_not_reaped;
                        goto resume_task;
                    }
                }
                else if (magic == EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC) {
                    retry_after_this = true;
                }
                else if (magic == CANCELLED_OP_IO_URING_DATA_MAGIC) {
                    /* Used when a SQE has been retrieved but the task has
                     * been cancelled and the SQE needs to be filled with
                     * something, which will be an io_uring noop with this
                     * magic. */
                    retry_after_this = true;
                }
            }
#if MONAD_ASYNC_EXECUTOR_PRINTING
            printf(
                "*** Executor %p has dequeued %u completions from "
                "io_uring\n",
                (void *)ex,
                i);
#endif
            io_uring_cq_advance(ring, i);
            monad_async_cpu_ticks_count_t const io_uring_end =
                get_ticks_count(memory_order_relaxed);
            ex->head.total_ticks_in_io_uring += io_uring_end - io_uring_begin;
        }
        else {
            // If io_uring was not enabled for this executor, use the
            // eventfd as the synchronisation object
            if (timeout == nullptr) {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p waits forever due to infinite "
                    "timeout\n",
                    (void *)ex);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                monad_async_cpu_ticks_count_t const sleep_begin =
                    get_ticks_count(memory_order_relaxed);
                int r = ppoll(fds, 1, nullptr, nullptr);
                monad_async_cpu_ticks_count_t const sleep_end =
                    get_ticks_count(memory_order_relaxed);
                ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
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
                    (void *)ex);
#endif
            }
            else {
#if MONAD_ASYNC_EXECUTOR_PRINTING
                printf(
                    "*** Executor %p waits for a non-infinite "
                    "timeout "
                    "%ld-%ld\n",
                    (void *)ex,
                    timeout->tv_sec,
                    timeout->tv_nsec);
#endif
                struct pollfd fds[1] = {
                    {.fd = ex->eventfd, .events = POLLIN, .revents = 0}};
                monad_async_cpu_ticks_count_t const sleep_begin =
                    get_ticks_count(memory_order_relaxed);
                int r = ppoll(fds, 1, timeout, nullptr);
                monad_async_cpu_ticks_count_t const sleep_end =
                    get_ticks_count(memory_order_relaxed);
                ex->head.total_ticks_sleeping = sleep_end - sleep_begin;
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
        while (ex->tasks_exited.count > 0) {
            struct monad_async_task_impl *task = ex->tasks_exited.front;
            LIST_REMOVE(ex->tasks_exited, task, (size_t *)nullptr);
            atomic_store_explicit(
                &task->head.current_executor, nullptr, memory_order_release);
            if (task->call_after_suspend_to_executor != nullptr) {
                monad_async_result (*call_after_suspend_to_executor)(
                    struct monad_async_task_impl *task) =
                    task->call_after_suspend_to_executor;
                task->call_after_suspend_to_executor = nullptr;
                MONAD_ASYNC_TRY_RESULT(, call_after_suspend_to_executor(task));
            }
        }
        if (atomic_load_explicit(
                &ex->cause_run_to_return, memory_order_acquire) != nullptr) {
            atomic_lock(&ex->lock);
            monad_async_result r = ex->cause_run_to_return_value;
            atomic_store_explicit(
                &ex->cause_run_to_return, nullptr, memory_order_release);
            atomic_unlock(&ex->lock);
            return r;
        }
        struct resume_tasks_state resume_tasks_state = {
            .ex = ex,
            .global_max_items = &max_items,
            .local_max_items =
                ex->tasks_suspended_completed[monad_async_priority_high].count +
                ex->tasks_suspended_completed[monad_async_priority_normal]
                    .count +
                ex->tasks_suspended_completed[monad_async_priority_low].count,
            .wait_list = ex->tasks_suspended_completed};
        if (max_items > 0) {
            monad_async_cpu_ticks_count_t const completions_begin =
                get_ticks_count(memory_order_relaxed);
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
                    monad_async_context_switcher task_switcher =
                        atomic_load_explicit(
                            &task->context->switcher, memory_order_acquire);
                    MONAD_ASYNC_TRY_RESULT(
                        ,
                        task_switcher->resume_many(
                            task_switcher,
                            monad_async_executor_impl_resume_tasks,
                            &resume_tasks_state));
                    if (resume_tasks_state.items >= max_items) {
                        max_items = 0;
                    }
                    else {
                        max_items -= resume_tasks_state.items;
                    }
                    break;
                }
            }
            monad_async_cpu_ticks_count_t const completions_end =
                get_ticks_count(memory_order_relaxed);
            ex->head.total_ticks_in_task_completion =
                completions_end - completions_begin;
            while (ex->tasks_exited.count > 0) {
                struct monad_async_task_impl *task = ex->tasks_exited.front;
                LIST_REMOVE(ex->tasks_exited, task, (size_t *)nullptr);
                atomic_store_explicit(
                    &task->head.current_executor,
                    nullptr,
                    memory_order_release);
                if (task->call_after_suspend_to_executor != nullptr) {
                    monad_async_result (*call_after_suspend_to_executor)(
                        struct monad_async_task_impl *task) =
                        task->call_after_suspend_to_executor;
                    task->call_after_suspend_to_executor = nullptr;
                    MONAD_ASYNC_TRY_RESULT(
                        , call_after_suspend_to_executor(task));
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
    return (timed_out && timeout_ != nullptr) ? monad_async_make_failure(ETIME)
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
    monad_async_cpu_ticks_count_t const run_begin =
        get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p enters run\n", (void *)ex);
#endif
    monad_async_result ret =
        monad_async_executor_run_impl(ex, max_items, timeout);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p exits run having processed %zu items\n",
        (void *)ex,
        ret.value);
#endif
    monad_async_cpu_ticks_count_t const run_end =
        get_ticks_count(memory_order_relaxed);
    ex->head.total_ticks_in_run += run_end - run_begin;
    ex->within_run = false;
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    return ret;
}

monad_async_result monad_async_executor_suspend_impl(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    monad_async_result (*please_cancel)(struct monad_async_task_impl *task),
    monad_async_io_status **completed)
{
    assert(atomic_load_explicit(&task->head.is_running, memory_order_acquire));
    assert(
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) ==
        &task->head);
    atomic_store_explicit(
        &ex->head.current_task, nullptr, memory_order_release);
    task->please_cancel = please_cancel;
    task->completed = completed;
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
    printf("*** Executor %p suspends task %p\n", (void *)ex, (void *)task);
#endif
    atomic_load_explicit(&task->context->switcher, memory_order_acquire)
        ->suspend_and_call_resume(task->context, nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Executor %p resumes task %p (cpu priority=%d, i/o priority=%d)\n",
        (void *)ex,
        (void *)task,
        (int)task->head.priority.cpu,
        (int)task->head.priority.io);
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
    task->please_cancel_invoked =
        false; // result of task resumption already is set
    task->please_cancel = nullptr;
    task->completed = nullptr;
    return task->head.result;
}

monad_async_result monad_async_executor_wake(
    monad_async_executor ex_, monad_async_result const *cause_run_to_return)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    atomic_lock(&ex->lock);
    monad_async_result r =
        monad_async_executor_wake_impl(&ex->lock, ex, cause_run_to_return);
    atomic_unlock(&ex->lock);
    return r;
}

monad_async_result monad_async_executor_claim_registered_io_buffer(
    monad_async_executor_registered_io_buffer *buffer, monad_async_executor ex_,
    size_t bytes_requested, bool is_for_write)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    if (bytes_requested > 2 * 1024 * 1024) {
        assert(false);
        return monad_async_make_failure(EINVAL);
    }
    bool const is_large_page = (bytes_requested > 4096);
    if (ex->registered_buffers[is_for_write].free[is_large_page] == nullptr) {
        return monad_async_make_failure(ENOMEM);
    }
    struct monad_async_executor_free_registered_buffer *p =
        ex->registered_buffers[is_for_write].free[is_large_page];
    ex->registered_buffers[is_for_write].free[is_large_page] = p->next;
    buffer->index = is_for_write ? -(int)p->index : (int)p->index;
    buffer->iov[0].iov_base = (void *)p;
    buffer->iov[0].iov_len = is_large_page ? (2 * 1024 * 1024) : 4096;
    return monad_async_make_success(0);
}

monad_async_result monad_async_executor_release_registered_io_buffer(
    monad_async_executor ex_, int buffer_index)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)ex_;
    bool const is_for_write = (buffer_index < 0);
    if (is_for_write) {
        buffer_index = -buffer_index;
    }
    if (buffer_index <= 0 ||
        (unsigned)buffer_index > ex->registered_buffers[is_for_write].size) {
        assert(false);
        return monad_async_make_failure(EINVAL);
    }
    struct iovec *iov =
        &ex->registered_buffers[is_for_write].buffers[buffer_index - 1];
    bool const is_large_page = (iov->iov_len > 4096);
    struct monad_async_executor_free_registered_buffer *p =
        (struct monad_async_executor_free_registered_buffer *)iov->iov_base;
    p->index = (unsigned)buffer_index;
    p->next = ex->registered_buffers[is_for_write].free[is_large_page];
    ex->registered_buffers[is_for_write].free[is_large_page] = p;
    return monad_async_make_success(0);
}

void monad_async_executor_task_detach(monad_async_task task_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (!atomic_load_explicit(
            &task_->is_running_on_foreign_executor, memory_order_acquire)) {
        assert(atomic_load_explicit(&task_->is_running, memory_order_acquire));
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)atomic_load_explicit(
                &task->head.current_executor, memory_order_acquire);
        assert(
            atomic_load_explicit(
                &ex->head.current_task, memory_order_acquire) == task_);
        atomic_store_explicit(
            &ex->head.current_task, nullptr, memory_order_release);
        task_->ticks_when_detached = get_ticks_count(memory_order_relaxed);
        task_->total_ticks_executed +=
            task_->ticks_when_detached - task_->ticks_when_resumed;
        atomic_store_explicit(&task_->is_running, false, memory_order_release);
        atomic_lock(&ex->lock);
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_running[task->head.priority.cpu],
            task,
            &ex->head.tasks_running);
        LIST_APPEND(ex->tasks_exited, task, (size_t *)nullptr);
        atomic_unlock(&ex->lock);
    }
}

/****************************************************************************/

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
                "thread on which its executor is run.\n");
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
    monad_async_context_switcher task_switcher =
        atomic_load_explicit(&task->context->switcher, memory_order_acquire);
    if (opt_reparent_switcher && opt_reparent_switcher != task_switcher) {
        monad_async_context_reparent_switcher(
            task->context, opt_reparent_switcher);
        task_switcher = opt_reparent_switcher;
    }
    atomic_store_explicit(
        &task->head.current_executor,
        (monad_async_executor)ex,
        memory_order_release);
    atomic_store_explicit(
        &task->head.is_pending_launch, true, memory_order_release);
    atomic_store_explicit(
        &task->head.is_awaiting_dispatch, false, memory_order_release);
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
            monad_async_executor_wake_impl(&ex->lock, ex, nullptr));
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
            &task->head.is_suspended_awaiting, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion, memory_order_acquire) ||
        atomic_load_explicit(
            &task->head.is_suspended_sqe_exhaustion_wr, memory_order_acquire)) {
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

monad_async_result monad_async_task_set_priorities(
    monad_async_task task_, monad_async_priority cpu, monad_async_priority io)
{
    if (io != monad_async_priority_unchanged) {
        task_->priority.io = io;
    }
    if (cpu == monad_async_priority_unchanged) {
        return monad_async_make_success(0);
    }
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_running[task->head.priority.cpu],
            task,
            &ex->head.tasks_running);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_awaiting, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_suspended_awaiting[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    task->head.priority.cpu = cpu;
    if (atomic_load_explicit(&task->head.is_running, memory_order_acquire)) {
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_running[task->head.priority.cpu],
            task,
            &ex->head.tasks_running);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_awaiting, memory_order_acquire)) {
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_suspended_awaiting[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    else if (atomic_load_explicit(
                 &task->head.is_suspended_completed, memory_order_acquire)) {
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_suspended_completed[task->head.priority.cpu],
            task,
            &ex->head.tasks_suspended);
    }
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_io_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task != *(struct monad_async_task_impl **)&iostatus->result) {
        return monad_async_make_failure(ENOENT);
    }
    if (iostatus->cancel_ == nullptr) {
        return monad_async_make_failure(EAGAIN);
    }
    return iostatus->cancel_(task_, iostatus);
}

monad_async_io_status *monad_async_task_completed_io(monad_async_task task_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    monad_async_io_status *ret = task->io_completed.front;
    if (ret == nullptr) {
        return ret;
    }
    ret->ticks_when_reaped = get_ticks_count(memory_order_relaxed);
    LIST_REMOVE(task->io_completed, ret, &task->head.io_completed_not_reaped);
    return ret;
}

static inline monad_async_result
monad_async_task_suspend_for_duration_cancel(struct monad_async_task_impl *task)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task, false);
    io_uring_prep_timeout_remove(
        sqe, (__u64)io_uring_mangle_into_data(task), 0);
    return monad_async_make_success(EAGAIN); // Canceller needs to wait
}

monad_async_result monad_async_task_suspend_for_duration(
    monad_async_io_status **completed, monad_async_task task_, uint64_t ns)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_invoked) {
        return monad_async_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    // timespec must live until resumption
    struct __kernel_timespec ts;
    if (ns != (uint64_t)-1 || completed == nullptr) {
        struct io_uring_sqe *sqe =
            get_sqe_suspending_if_necessary(ex, task, true);
        if (sqe == nullptr) {
            assert(task->please_cancel_invoked);
            return monad_async_make_failure(ECANCELED);
        }
        if (ns == 0) {
            io_uring_prep_nop(sqe);
        }
        else {
            ts.tv_sec = (long long)(ns / 1000000000);
            ts.tv_nsec = (long long)(ns % 1000000000);
            io_uring_prep_timeout(sqe, &ts, 0, 0);
        }
        io_uring_sqe_set_data(sqe, task, task);
    }

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "suspend_for_duration ns=%lu completed=%p *completed=%p\n",
        (void *)task,
        (void *)ex,
        ns,
        (void *)completed,
        completed ? (void *)*completed : nullptr);
#endif
    monad_async_result ret = monad_async_executor_suspend_impl(
        ex, task, monad_async_task_suspend_for_duration_cancel, completed);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "suspend_for_duration *completed=%p\n",
        (void *)task,
        (void *)ex,
        completed ? (void *)*completed : nullptr);
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
