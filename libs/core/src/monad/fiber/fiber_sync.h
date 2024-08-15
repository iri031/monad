#pragma once

/**
 * @file
 *
 * This file defines a simple wait_queue structure, shared by several of the
 * synchronization primitives
 */

#include <errno.h>
#include <string.h>
#include <sys/queue.h>
#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/fiber/fiber.h>

typedef struct monad_fiber_wait_queue monad_fiber_wait_queue_t;

struct monad_fiber_wait_queue {
    monad_spinlock_t *lock;                    ///< Protects waiting_fibers
    TAILQ_HEAD(, monad_fiber) waiting_fibers;  ///< List of fibers waiting
    char name[MONAD_FIBER_NAME_LEN + 1];       ///< Human-readable debug name
#if MONAD_FIBER_DEBUG_LEVEL > 0
    monad_source_location srcloc;              ///< Location where declared
#endif
};

static inline void
monad_fiber_wait_queue_init(monad_fiber_wait_queue_t *wq,
                            monad_spinlock_t *lock,
                            [[maybe_unused]] monad_source_location_t sl) {
    wq->lock = lock;
    TAILQ_INIT(&wq->waiting_fibers);
#if MONAD_FIBER_DEBUG_LEVEL > 0
    wq->srcloc = sl;
#endif
}

static inline void monad_wait_queue_try_wakeup(monad_fiber_wait_queue_t *wq) {
    monad_fiber_t *waiter;
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(wq->lock));
    if (!TAILQ_EMPTY(&wq->waiting_fibers)) {
        // There is at least one fiber waiting for a value; try to wake it up
        waiter = TAILQ_FIRST(&wq->waiting_fibers);
        const bool woke_up = _monad_fiber_try_wakeup(waiter, wq);
        MONAD_ASSERT(woke_up);
    } else
        monad_spinlock_unlock(wq->lock);
}

static inline int
monad_fiber_wait_queue_set_name(monad_fiber_wait_queue_t *wq, const char *name)
{
    if (name == nullptr)
        return EFAULT;
    // XXX: not thread-safe, who cares?
    (void)strncpy(wq->name, name, MONAD_FIBER_NAME_LEN);
    return strlen(name) > MONAD_FIBER_NAME_LEN ? ENAMETOOLONG : 0;
}
