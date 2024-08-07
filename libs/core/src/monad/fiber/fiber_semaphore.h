#pragma once

/**
 * @file
 *
 * This file implements a semaphore object used with monad_fiber
 */

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct monad_fiber_semaphore monad_fiber_semaphore_t;

static inline void monad_fiber_semaphore_init(monad_fiber_semaphore_t *sem);

static inline void monad_fiber_semaphore_wait(monad_fiber_semaphore_t *sem,
                                              monad_fiber_prio_t wakeup_prio);

static inline void monad_fiber_semaphore_signal(monad_fiber_semaphore_t *sem);

struct monad_fiber_semaphore {
    alignas(64) spinlock_t lock;                ///< Protects all lists
    unsigned tokens;                            ///< Immediate wakeup tokens
    monad_fiber_wait_queue_t waiting_fibers;    ///< List of waiting fibers
};

static inline void monad_fiber_semaphore_init(monad_fiber_semaphore_t *sem) {
    spinlock_init(&sem->lock);
    sem->tokens = 0;
    TAILQ_INIT(&sem->waiting_fibers);
}

void monad_fiber_semaphore_wait(monad_fiber_semaphore_t *sem,
                                monad_fiber_prio_t wakeup_prio) {
    spinlock_lock(&sem->lock);
TryAgain:
    if (sem->tokens > 0) {
        --sem->tokens;
        spinlock_unlock(&sem->lock);
        return;
    }

    // No token available; sleep on this channel and suspend our fiber. We'll
    // be resumed later when someone else calls the signal routine, which will
    // reschedule us to become runnable again, with the specified priority
    _monad_fiber_sleep(&sem->waiting_fibers, &sem->lock, wakeup_prio);
    MONAD_ASSERT(spinlock_is_owned(&sem->lock));
    goto TryAgain;
}

void monad_fiber_semaphore_signal(monad_fiber_semaphore_t *sem) {
    monad_fiber_t *waiter;

    spinlock_lock(&sem->lock);
    ++sem->tokens;
    if (!TAILQ_EMPTY(&sem->waiting_fibers)) {
        // There is at least one fiber waiting for a value; reschedule it
        // on the last run queue it was associated with
        waiter = TAILQ_FIRST(&sem->waiting_fibers);
        _monad_fiber_wakeup(waiter, &sem->waiting_fibers, &sem->lock);
    } else {
        spinlock_unlock(&sem->lock);
    }
}

#ifdef __cplusplus
} // extern "C"
#endif
