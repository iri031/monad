#pragma once

/**
 * @file
 *
 * This file implements a semaphore object used with monad_fiber
 */

#include <stddef.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_sync.h>

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct monad_fiber_semaphore monad_fiber_semaphore_t;

/// Initialize a semaphore, given its location in the source code for easier
/// debugging (this is only stored if a compile-time option is enabled)
static void monad_fiber_semaphore_init(
    monad_fiber_semaphore_t *sem, monad_source_location_t srcloc);

/// Acquire a wakeup token from the semaphore; this operation is conventionally
/// called "wait" (or 'P') in the literature because, if a wakeup token is not
/// available immediately, the caller will sleep
static void monad_fiber_semaphore_acquire(
    monad_fiber_semaphore_t *sem, monad_fiber_prio_t wakeup_prio);

/// A non-blocking form of acquire; the wakeup token will be consumed if
/// available, and the return value will indicate what happened
static bool monad_fiber_semaphore_try_acquire(monad_fiber_semaphore_t *sem);

/// Release the given number of wakeup tokens, potentially waking up waiting
/// fibers if there are any; this operation is also conventionally called
/// "signal" (or 'V')
static void monad_fiber_semaphore_release(
    monad_fiber_semaphore_t *sem, unsigned num_tokens);

/// Get the name of a semaphore, for debugging and instrumentation
static int monad_fiber_semaphore_get_name(
    monad_fiber_semaphore_t *sem, char *name, size_t size);

/// Set the name of a semaphore, for debugging and instrumentation
static int
monad_fiber_semaphore_set_name(monad_fiber_semaphore_t *sem, char const *name);

struct monad_fiber_semaphore
{
    alignas(64) monad_spinlock_t lock;     ///< Protects all members
    unsigned tokens;                       ///< Immediate wakeup tokens
    monad_fiber_wait_queue_t wait_queue;   ///< List of waiting fibers
};

inline void monad_fiber_semaphore_init(
    monad_fiber_semaphore_t *sem, monad_source_location_t srcloc)
{
    monad_spinlock_init(&sem->lock);
    sem->tokens = 0;
    monad_fiber_wait_queue_init(&sem->wait_queue, &sem->lock, srcloc);
}

inline void monad_fiber_semaphore_acquire(
    monad_fiber_semaphore_t *sem, monad_fiber_prio_t wakeup_prio)
{
    MONAD_SPINLOCK_LOCK(&sem->lock);
TryAgain:
    if (sem->tokens > 0) {
        --sem->tokens;
        MONAD_SPINLOCK_UNLOCK(&sem->lock);
        return;
    }

    // No token available; sleep on this channel and suspend our fiber. We'll
    // be resumed later when someone else calls the signal routine, which will
    // reschedule us to become runnable again, with the specified priority
    _monad_exec_sleep(&sem->wait_queue, wakeup_prio);
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&sem->lock));
    goto TryAgain;
}

inline bool monad_fiber_semaphore_try_acquire(monad_fiber_semaphore_t *sem)
{
    bool has_token = false;
    MONAD_SPINLOCK_LOCK(&sem->lock);
    if (MONAD_LIKELY(sem->tokens > 0)) {
        --sem->tokens;
        has_token = true;
    }
    MONAD_SPINLOCK_UNLOCK(&sem->lock);
    return has_token;
}

inline void
monad_fiber_semaphore_release(monad_fiber_semaphore_t *sem, unsigned num_tokens)
{
    // The reason for this odd loop structure and the continuous re-locking
    // of `sem->lock` is that the wait queue is always unlocked inside
    // monad_wait_queue_try_wakeup; that is a performance optimization to let
    // go of the wait queue immediately to allow contending users to grab
    // it while the fiber wakeup rescheduling code is running
    while (num_tokens > 0) {
        MONAD_SPINLOCK_LOCK(&sem->lock);
        ++sem->tokens;
        monad_wait_queue_try_wakeup(&sem->wait_queue);
        --num_tokens;
    }
}

inline int monad_fiber_semaphore_get_name(
    monad_fiber_semaphore_t *sem, char *name, size_t size)
{
    return monad_fiber_wait_queue_get_name(&sem->wait_queue, name, size);
}

inline int
monad_fiber_semaphore_set_name(monad_fiber_semaphore_t *sem, char const *name)
{
    return monad_fiber_wait_queue_set_name(&sem->wait_queue, name);
}

#ifdef __cplusplus
} // extern "C"
#endif
