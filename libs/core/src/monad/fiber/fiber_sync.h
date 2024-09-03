#pragma once

/**
 * @file
 *
 * This file defines a simple wait_queue structure, shared by several of the
 * synchronization primitives
 */

#include <errno.h>
#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <string.h>
#include <sys/queue.h>

#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct monad_fiber_wait_queue monad_fiber_wait_queue_t;

extern void _monad_thread_executor_busy_wait(
    monad_thread_executor_t *thr_exec, monad_fiber_wait_queue_t *wq);

extern bool _monad_thread_executor_wakeup(
    monad_thread_executor_t *thr_exec, monad_fiber_wait_queue_t *wq);

struct monad_fiber_wait_queue
{
    monad_spinlock_t *lock;                     ///< Protects wait_list
    TAILQ_HEAD(, monad_exec_context) wait_list; ///< List of contexts
    char name[MONAD_FIBER_NAME_LEN + 1];        ///< Human-readable debug name
#if MONAD_FIBER_DEBUG_LEVEL > 0
    monad_source_location srcloc;               ///< Location where declared
#endif
};

/*
 * Private interface: these functions are only called by other parts of the
 * fiber library, e.g. by synchronization primitives like monad_fiber_channel_t
 */

/// Put the current execution context to sleep on the given wait queue, to be
/// woken up with the given priority
static void
_monad_exec_sleep(monad_fiber_wait_queue_t *wq, monad_fiber_prio_t wakeup_prio);

/// Wake up an execution context that was put to sleep on the given wait queue
/// via an earlier call to _monad_exec_sleep; for fibers, "wake up" means "cause
/// the fiber to be rescheduled"; this can fail, e.g., if the scheduler queue is
/// full
static bool _monad_exec_try_wakeup(
    struct monad_exec_context *exec_ctx, monad_fiber_wait_queue_t *wq);

static inline void monad_fiber_wait_queue_init(
    monad_fiber_wait_queue_t *wq, monad_spinlock_t *lock,
    [[maybe_unused]] monad_source_location_t sl)
{
    memset(wq, 0, sizeof *wq);
    wq->lock = lock;
    TAILQ_INIT(&wq->wait_list);
#if MONAD_FIBER_DEBUG_LEVEL > 0
    wq->srcloc = sl;
#endif
}

static inline void monad_wait_queue_try_wakeup(monad_fiber_wait_queue_t *wq)
{
    struct monad_exec_context *waiter;
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(wq->lock));
    if (!TAILQ_EMPTY(&wq->wait_list)) {
        // There is at least one execution context waiting for a value; try to
        // wake it up
        waiter = TAILQ_FIRST(&wq->wait_list);
        bool const woke_up = _monad_exec_try_wakeup(waiter, wq);
        MONAD_ASSERT(woke_up);
    }
    else {
        MONAD_SPINLOCK_UNLOCK(wq->lock);
    }
}

static inline int monad_fiber_wait_queue_get_name(
    monad_fiber_wait_queue_t *wq, char *name, size_t size)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(wq->lock);
    rc = strlcpy(name, wq->name, size) >= size ? ERANGE : 0;
    MONAD_SPINLOCK_UNLOCK(wq->lock);
    return rc;
}

static inline int
monad_fiber_wait_queue_set_name(monad_fiber_wait_queue_t *wq, char const *name)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(wq->lock);
    rc = strlcpy(wq->name, name, sizeof wq->name) > MONAD_FIBER_NAME_LEN
             ? ERANGE
             : 0;
    MONAD_SPINLOCK_UNLOCK(wq->lock);
    return rc;
}

inline void
_monad_exec_sleep(monad_fiber_wait_queue_t *wq, monad_fiber_prio_t wakeup_prio)
{
    monad_thread_executor_t *thr_exec;
    struct monad_exec_context *cur_exec;
    monad_fiber_t *cur_fiber;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(wq->lock));
    thr_exec = _monad_current_thread_executor();
    cur_fiber = thr_exec->cur_fiber;

    if (MONAD_LIKELY(cur_fiber != nullptr)) {
        MONAD_SPINLOCK_LOCK(&cur_fiber->lock);
        if (wakeup_prio != MONAD_FIBER_PRIO_NO_CHANGE) {
            cur_fiber->priority = wakeup_prio;
        }
        cur_exec = &cur_fiber->exec_ctx;
    }
    else {
        // This is an ordinary thread, not a fiber; In the current db
        // implementation, an ordinary thread of execution is sometimes treated
        // as though it is running on a fiber, so these can also wait. This is
        // an API idiom that Boost.Fiber allowed, thus the existing db code grew
        // to rely on it. A special implementation is used in this case.
        // TODO(ken): remove this work-around, by cleaning up the code that
        //   calls this
        cur_exec = &thr_exec->thread_ctx;
    }

    cur_exec->wait_queue = wq;
    TAILQ_INSERT_TAIL(&wq->wait_list, cur_exec, wait_link);
    MONAD_SPINLOCK_UNLOCK(wq->lock);
    ++cur_exec->stats->total_sleep;

    if (MONAD_LIKELY(cur_fiber != nullptr)) {
        _monad_suspend_fiber(
            cur_fiber, MF_STATE_WAIT_QUEUE, MF_SUSPEND_SLEEP, 0);
    }
    else {
        _monad_thread_executor_busy_wait(thr_exec, wq);
    }

    MONAD_SPINLOCK_LOCK(wq->lock);
}

inline bool _monad_exec_try_wakeup(
    struct monad_exec_context *exec_ctx, monad_fiber_wait_queue_t *wq)
{
    int rc;
    monad_fiber_t *fiber;

    TAILQ_REMOVE(&wq->wait_list, exec_ctx, wait_link);
    MONAD_SPINLOCK_UNLOCK(wq->lock);

    fiber = _monad_exec_context_to_fiber(exec_ctx);
    if (MONAD_UNLIKELY(fiber == nullptr)) {
        return _monad_thread_executor_wakeup(
            (monad_thread_executor_t *)exec_ctx, wq);
    }

    MONAD_SPINLOCK_LOCK(&fiber->lock);
    exec_ctx->state = MF_STATE_CAN_RUN;
    exec_ctx->prev_wq = exec_ctx->wait_queue;
    exec_ctx->wait_queue = nullptr;

    if (MONAD_UNLIKELY(fiber->run_queue == nullptr)) {
        // XXX: only for the test suite?
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return true;
    }
    if ((rc = monad_run_queue_try_push(fiber->run_queue, fiber)) == 0) {
        return true;
    }
    MONAD_ASSERT(rc != EBUSY);

    // Schedule failed because the run queue was too small; link us back
    // onto the wait queue
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    exec_ctx->state = MF_STATE_WAIT_QUEUE;
    exec_ctx->wait_queue = exec_ctx->prev_wq;
    exec_ctx->prev_wq = nullptr;
    ++fiber->stats.total_sleep;
    ++fiber->stats.total_spurious_wakeups;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);

    MONAD_SPINLOCK_LOCK(wq->lock);
    TAILQ_INSERT_HEAD(&wq->wait_list, exec_ctx, wait_link);
    MONAD_SPINLOCK_UNLOCK(wq->lock);
    return false;
}

#ifdef __cplusplus
} // extern "C"
#endif
