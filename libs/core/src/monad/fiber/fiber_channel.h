#pragma once

/**
 * @file
 *
 * This file implements the "channels" concurrent programming abstraction for
 * monad_fiber objects.
 */

#include <stddef.h>
#include <stdint.h>
#include <sys/queue.h>
#include <sys/uio.h>

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

typedef struct monad_fiber_channel monad_fiber_channel_t;
typedef struct monad_fiber_msghdr monad_fiber_msghdr_t;

// TODO(ken): https://github.com/monad-crypto/monad-internal/issues/498
#define MONAD_FIBER_MBUF_MAX_INTERNAL (32)

/// Initialize a channel, given its location in the source code for easier
/// debugging (this is only stored if a compile-time option is enabled)
static void monad_fiber_channel_init(
    monad_fiber_channel_t *channel, monad_source_location_t srcloc);

/// Push a message onto a channel; if a fiber is waiting for a message because
/// of a previous call to `monad_fiber_channel_pop`, that fiber will be
/// rescheduled to run as a result of this call
static void monad_fiber_channel_push(
    monad_fiber_channel_t *channel, monad_fiber_msghdr_t *msghdr);

/// Try to pop a message from the channel; "try" means that this is a
/// non-blocking call: if nothing is available, nullptr is returned immediately
static monad_fiber_msghdr_t *
monad_fiber_channel_try_pop(monad_fiber_channel_t *channel);

/// Pop a message from the channel; this may sleep if no messages are available;
/// if we are put to sleep, we will be rescheduled with the given wakeup
/// priority
static monad_fiber_msghdr_t *monad_fiber_channel_pop(
    monad_fiber_channel_t *channel, monad_fiber_prio_t wakeup_prio);

/// Get the name of a channel, for debugging and instrumentation
static int monad_fiber_channel_get_name(
    monad_fiber_channel_t *channel, char *name, size_t size);

/// Set the name of a channel, for debugging and instrumentation
static int
monad_fiber_channel_set_name(monad_fiber_channel_t *channel, char const *name);

/// Initialize a message header whose content buffer is described by the given
/// `struct iovec` memory area
static void
monad_fiber_msghdr_init(monad_fiber_msghdr_t *m, struct iovec const iov);

/// Initialize a message whose content memory area defined is defined by
/// [(uint8_t const*)(m + 1), ((uint8_t const*)(m + 1) + trailing_size)
static void
monad_fiber_msghdr_init_trailing(monad_fiber_msghdr_t *m, size_t trailing_size);

/// Descriptor for a message enqueued on a channel; see the fiber-api.md
/// documentation section on memory management for an explanation of this
/// object
struct monad_fiber_msghdr
{
    TAILQ_ENTRY(monad_fiber_msghdr) link; ///< Linkage to next msghdr in list
    struct iovec msg_buf; ///< Buffer storing message payload
};

struct monad_fiber_channel
{
    alignas(64) monad_spinlock_t lock; ///< Protects all members
    TAILQ_HEAD(, monad_fiber_msghdr) ready_msgs; ///< List of ready messages
    monad_fiber_wait_queue_t wait_queue; ///< List of waiting fibers
};

inline void monad_fiber_channel_init(
    monad_fiber_channel_t *channel, monad_source_location_t srcloc)
{
    monad_spinlock_init(&channel->lock);
    TAILQ_INIT(&channel->ready_msgs);
    monad_fiber_wait_queue_init(&channel->wait_queue, &channel->lock, srcloc);
}

inline void monad_fiber_channel_push(
    monad_fiber_channel_t *channel, monad_fiber_msghdr_t *m)
{
    MONAD_SPINLOCK_LOCK(&channel->lock);
    TAILQ_INSERT_TAIL(&channel->ready_msgs, m, link);
    monad_wait_queue_try_wakeup(&channel->wait_queue);
}

inline monad_fiber_msghdr_t *
monad_fiber_channel_try_pop(monad_fiber_channel_t *channel)
{
    monad_fiber_msghdr_t *msghdr = nullptr;
    MONAD_SPINLOCK_LOCK(&channel->lock);
    if (MONAD_LIKELY(!TAILQ_EMPTY(&channel->ready_msgs))) {
        msghdr = TAILQ_FIRST(&channel->ready_msgs);
        TAILQ_REMOVE(&channel->ready_msgs, msghdr, link);
    }
    MONAD_SPINLOCK_UNLOCK(&channel->lock);
    return msghdr;
}

inline monad_fiber_msghdr_t *monad_fiber_channel_pop(
    monad_fiber_channel_t *channel, monad_fiber_prio_t wakeup_prio)
{
    monad_fiber_msghdr_t *msghdr;

    MONAD_SPINLOCK_LOCK(&channel->lock);
TryAgain:
    if (MONAD_LIKELY(!TAILQ_EMPTY(&channel->ready_msgs))) {
        // A message is ready immediately; hand it back
        msghdr = TAILQ_FIRST(&channel->ready_msgs);
        TAILQ_REMOVE(&channel->ready_msgs, msghdr, link);
        MONAD_SPINLOCK_UNLOCK(&channel->lock);
        return msghdr;
    }

    // No value is ready; sleep on this channel and suspend our fiber. We'll
    // be resumed later when someone else calls the push routine, which will
    // reschedule us to become runnable again, with the specified priority
    _monad_exec_sleep(&channel->wait_queue, wakeup_prio);
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&channel->lock));
    goto TryAgain;
}

inline int monad_fiber_channel_get_name(
    monad_fiber_channel_t *channel, char *name, size_t size)
{
    return monad_fiber_wait_queue_get_name(&channel->wait_queue, name, size);
}

inline int
monad_fiber_channel_set_name(monad_fiber_channel_t *channel, char const *name)
{
    return monad_fiber_wait_queue_set_name(&channel->wait_queue, name);
}

inline void
monad_fiber_msghdr_init(monad_fiber_msghdr_t *m, struct iovec const iov)
{
    MONAD_DEBUG_ASSERT(m != nullptr);
    memset(m, 0, sizeof *m);
    m->msg_buf = iov;
}

inline void
monad_fiber_msghdr_init_trailing(monad_fiber_msghdr_t *m, size_t trailing_size)
{
    struct iovec const iov = {.iov_base = m + 1, .iov_len = trailing_size};
    monad_fiber_msghdr_init(m, iov);
}

#ifdef __cplusplus
} // extern "C"
#endif
