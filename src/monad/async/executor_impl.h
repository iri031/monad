#pragma once

#include "task_impl.h"

#include <stdio.h>
#include <threads.h>

#include <poll.h>
#include <sys/eventfd.h>
#include <unistd.h>

#if MONAD_ASYNC_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif

struct monad_async_executor_impl
{
    struct monad_async_executor_head head;

    thrd_t owning_thread;
    bool within_run;
    atomic_bool need_to_empty_eventfd;
    monad_async_context run_context;
    struct io_uring ring, wr_ring;
    LIST_DEFINE_P(tasks_running, struct monad_async_task_impl);
    LIST_DEFINE_P(tasks_suspended_awaiting, struct monad_async_task_impl);
    LIST_DEFINE_P(tasks_suspended_completed, struct monad_async_task_impl);
    monad_async_result *_Atomic cause_run_to_return;

    // all items below this require taking the lock
    atomic_int lock;
    int eventfd;
    monad_async_priority tasks_pending_launch_next_queue;
    // Note NOT sorted by task priority!
    LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
    monad_async_result cause_run_to_return_value;
};

// diseased dead beef in hex, last bit set so won't be a pointer
static void *const EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC =
    (void *)(uintptr_t)0xd15ea5eddeadbeef;

static inline void atomic_lock(atomic_int *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_lock(lock, __tsan_mutex_try_lock);
#endif
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
        lock, &expected, 1, memory_order_acq_rel, memory_order_relaxed)) {
        thrd_yield();
        expected = 0;
    }
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_lock(lock, __tsan_mutex_try_lock, 0);
#endif
}

static inline void atomic_unlock(atomic_int *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_unlock(lock, __tsan_mutex_try_lock);
#endif
    atomic_store_explicit(lock, 0, memory_order_release);
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_unlock(lock, __tsan_mutex_try_lock);
#endif
}

static inline int mutex_lock(mtx_t *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_lock(lock, __tsan_mutex_try_lock);
#endif
    int r = mtx_lock(lock);
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_lock(lock, __tsan_mutex_try_lock, 0);
#endif
    return r;
}

static inline int mutex_unlock(mtx_t *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_unlock(lock, __tsan_mutex_try_lock);
#endif
    int r = mtx_unlock(lock);
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_unlock(lock, __tsan_mutex_try_lock);
#endif
    return r;
}

static inline int64_t timespec_to_ns(const struct timespec *a)
{
    return ((int64_t)a->tv_sec * 1000000000LL) + (int64_t)a->tv_nsec;
}

static inline int64_t
timespec_diff(const struct timespec *a, const struct timespec *b)
{
    return timespec_to_ns(a) - timespec_to_ns(b);
}

static inline monad_async_result monad_async_executor_create_impl(
    struct monad_async_executor_impl *p, struct monad_async_executor_attr *attr)
{
    p->owning_thread = thrd_current();
    p->eventfd = eventfd(0, EFD_CLOEXEC);
    if (-1 == p->eventfd) {
        return monad_async_make_failure(errno);
    }
    if (attr->io_uring_ring.entries > 0) {
        int r = io_uring_queue_init_params(
            attr->io_uring_ring.entries, &p->ring, &attr->io_uring_ring.params);
        if (r < 0) {
            return monad_async_make_failure(-r);
        }
        if (attr->io_uring_wr_ring.entries > 0) {
            r = io_uring_queue_init_params(
                attr->io_uring_wr_ring.entries,
                &p->wr_ring,
                &attr->io_uring_wr_ring.params);
            if (r < 0) {
                return monad_async_make_failure(-r);
            }
        }
        if (!(p->ring.features & IORING_FEAT_NODROP)) {
            fprintf(
                stderr,
                "FATAL: This kernel's io_uring implementation does not "
                "implement "
                "no-drop.\n");
            abort();
        }
        if (!(p->ring.features & IORING_FEAT_SUBMIT_STABLE)) {
            fprintf(
                stderr,
                "FATAL: This kernel's io_uring implementation does not "
                "implement "
                "stable submits.\n");
            abort();
        }
        struct io_uring_sqe *sqe = io_uring_get_sqe(&p->ring);
        if (sqe == nullptr) {
            abort(); // should never occur
        }
        io_uring_prep_poll_multishot(sqe, p->eventfd, POLLIN);
        io_uring_sqe_set_data(sqe, EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC);
        r = io_uring_submit(&p->ring);
        if (r < 0) {
            return monad_async_make_failure(-r);
        }
    }
    return monad_async_make_success(0);
}

static inline monad_async_result
monad_async_executor_destroy_impl(struct monad_async_executor_impl *ex)
{
    if (!thrd_equal(thrd_current(), ex->owning_thread)) {
        fprintf(
            stderr,
            "FATAL: You must destroy an executor from the same kernel thread "
            "which owns it.\n");
        abort();
    }
    // Any tasks still executing must be cancelled
    atomic_lock(&ex->lock);
    for (monad_async_priority priority = monad_async_priority_high;
         priority < monad_async_priority_max;
         priority++) {
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_pending_launch[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_running[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_suspended_awaiting[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_suspended_completed[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
    }
    atomic_unlock(&ex->lock);
    if (ex->wr_ring.ring_fd != 0) {
        io_uring_queue_exit(&ex->wr_ring);
    }
    if (ex->ring.ring_fd != 0) {
        io_uring_queue_exit(&ex->ring);
    }
    if (ex->eventfd != -1) {
        close(ex->eventfd);
        ex->eventfd = -1;
    }
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_wake_impl(
    atomic_int * /*lock must be held on entry*/,
    struct monad_async_executor_impl *ex,
    monad_async_result const *cause_run_to_return)
{
    if (cause_run_to_return != nullptr) {
        ex->cause_run_to_return_value = *cause_run_to_return;
        atomic_store_explicit(
            &ex->cause_run_to_return,
            &ex->cause_run_to_return_value,
            memory_order_release);
    }
    atomic_store_explicit(
        &ex->need_to_empty_eventfd, true, memory_order_release);
    if (-1 == eventfd_write(ex->eventfd, 1)) {
        return monad_async_make_success(errno);
    }
    return monad_async_make_success(0);
}
