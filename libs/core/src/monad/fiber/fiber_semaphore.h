#pragma once

/**
 * @file
 *
 * This file implements a semaphore object used with monad_fiber
 */

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_sync.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct monad_fiber_semaphore monad_fiber_semaphore_t;

static inline void monad_fiber_semaphore_init(monad_fiber_semaphore_t *sem,
                                              monad_source_location_t srcloc);

static inline void monad_fiber_semaphore_wait(monad_fiber_semaphore_t *sem,
                                              monad_fiber_prio_t wakeup_prio);

static inline bool monad_fiber_semaphore_try_consume(monad_fiber_semaphore_t *sem);

static inline void monad_fiber_semaphore_signal(monad_fiber_semaphore_t *sem);

static inline int monad_fiber_semaphore_set_name(monad_fiber_semaphore_t *sem,
                                                 const char *name);

struct monad_fiber_semaphore {
    alignas(64) monad_spinlock_t lock;     ///< Protects all members
    unsigned tokens;                       ///< Immediate wakeup tokens
    monad_fiber_wait_queue_t wait_queue;   ///< List of waiting fibers
};

static inline void monad_fiber_semaphore_init(monad_fiber_semaphore_t *sem,
                                              monad_source_location_t srcloc) {
    monad_spinlock_init(&sem->lock);
    sem->tokens = 0;
    monad_fiber_wait_queue_init(&sem->wait_queue, &sem->lock, srcloc);
}

void monad_fiber_semaphore_wait(monad_fiber_semaphore_t *sem,
                                monad_fiber_prio_t wakeup_prio) {
    MONAD_SPINLOCK_LOCK(&sem->lock);
TryAgain:
    if (sem->tokens > 0) {
        --sem->tokens;
        monad_spinlock_unlock(&sem->lock);
        return;
    }

    // No token available; sleep on this channel and suspend our fiber. We'll
    // be resumed later when someone else calls the signal routine, which will
    // reschedule us to become runnable again, with the specified priority
    _monad_fiber_sleep(&sem->wait_queue, wakeup_prio);
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&sem->lock));
    goto TryAgain;
}

bool monad_fiber_semaphore_try_consume(monad_fiber_semaphore_t *sem) {
    bool has_token = false;
    MONAD_SPINLOCK_LOCK(&sem->lock);
    if (sem->tokens > 0) [[likely]] {
        --sem->tokens;
        has_token = true;
    }
    monad_spinlock_unlock(&sem->lock);
    return has_token;
}

void monad_fiber_semaphore_signal(monad_fiber_semaphore_t *sem) {
    MONAD_SPINLOCK_LOCK(&sem->lock);
    ++sem->tokens;
    monad_wait_queue_try_wakeup(&sem->wait_queue);
}

static inline int monad_fiber_semaphore_set_name(monad_fiber_semaphore_t *sem,
                                                 const char *name) {
    return monad_fiber_wait_queue_set_name(&sem->wait_queue, name);
}

#ifdef __cplusplus
} // extern "C"
#endif
