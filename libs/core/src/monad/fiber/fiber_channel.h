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
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_sync.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct monad_fiber_channel monad_fiber_channel_t;
typedef struct monad_fiber_vbuf monad_fiber_vbuf_t;

constexpr size_t MONAD_FIBER_VBUF_MAX_INTERNAL = 32;

static inline void monad_fiber_channel_init(monad_fiber_channel_t *channel,
                                            monad_source_location_t srcloc);

static inline void monad_fiber_channel_push(monad_fiber_channel_t *channel,
                                            monad_fiber_vbuf_t *vbuf);

static inline monad_fiber_vbuf_t*
monad_fiber_channel_pop(monad_fiber_channel_t *channel,
                        monad_fiber_prio_t wakeup_prio);

static inline int monad_fiber_channel_set_name(monad_fiber_channel_t *channel,
                                               const char *name);

static inline void monad_fiber_vbuf_init(monad_fiber_vbuf_t *vbuf,
                                         const struct iovec *iov);

static inline struct iovec monad_fiber_vbuf_data(monad_fiber_vbuf_t *vbuf);

enum monad_fiber_vbuf_type : uint8_t {
    MONAD_FIBER_VBUF_IN_PLACE, ///< Value stored in `in_place` array
    MONAD_FIBER_VBUF_EXTERNAL  ///< Value stored in memory of `external_buf`
};

/// Design document for vbufs is here:
///
///   https://github.com/monad-crypto/monad-internal/issues/384#issuecomment-2250820311
///
/// TODO(ken): this is in monad-internal, needs to be moved somewhere public
struct monad_fiber_vbuf {
    uintptr_t pool_ext;        ///< Opaque; for downstream pool allocators
    enum monad_fiber_vbuf_type vbuf_type;   ///< Discriminator for storage union
    TAILQ_ENTRY(monad_fiber_vbuf) link;     ///< Linkage to next vbuf in list
    union {
        struct iovec external_buf;
        uint8_t in_place[MONAD_FIBER_VBUF_MAX_INTERNAL];
    };
};

struct monad_fiber_channel {
    alignas(64) monad_spinlock_t lock;          ///< Protects all members
    TAILQ_HEAD(, monad_fiber_vbuf) ready_vbufs; ///< List of ready value buffers
    monad_fiber_wait_queue_t wait_queue;        ///< List of waiting fibers
};

static inline void monad_fiber_channel_init(monad_fiber_channel_t *channel,
                                            monad_source_location_t srcloc) {
    monad_spinlock_init(&channel->lock);
    TAILQ_INIT(&channel->ready_vbufs);
    monad_fiber_wait_queue_init(&channel->wait_queue, &channel->lock, srcloc);
}

void monad_fiber_channel_push(monad_fiber_channel_t *channel,
                              monad_fiber_vbuf_t *vbuf) {
    MONAD_SPINLOCK_LOCK(&channel->lock);
    TAILQ_INSERT_TAIL(&channel->ready_vbufs, vbuf, link);
    monad_wait_queue_try_wakeup(&channel->wait_queue);
}

monad_fiber_vbuf_t *monad_fiber_channel_pop(monad_fiber_channel_t *channel,
                                            monad_fiber_prio_t wakeup_prio) {
    monad_fiber_vbuf_t *vbuf;

    MONAD_SPINLOCK_LOCK(&channel->lock);
TryAgain:
    if (!TAILQ_EMPTY(&channel->ready_vbufs)) [[likely]] {
        // A value is ready immediately; hand it back
        vbuf = TAILQ_FIRST(&channel->ready_vbufs);
        TAILQ_REMOVE(&channel->ready_vbufs, vbuf, link);
        monad_spinlock_unlock(&channel->lock);
        return vbuf;
    }

    // No value is ready; sleep on this channel and suspend our fiber. We'll
    // be resumed later when someone else calls the push routine, which will
    // reschedule us to become runnable again, with the specified priority
    _monad_fiber_sleep(&channel->wait_queue, wakeup_prio);
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&channel->lock));
    goto TryAgain;
}

static inline int monad_fiber_channel_set_name(monad_fiber_channel_t *channel,
                                               const char *name) {
    return monad_fiber_wait_queue_set_name(&channel->wait_queue, name);
}

static inline void monad_fiber_vbuf_init(monad_fiber_vbuf_t *vbuf,
                                         const struct iovec *iov) {
    if (iov != nullptr) {
        vbuf->vbuf_type = MONAD_FIBER_VBUF_EXTERNAL;
        vbuf->external_buf = *iov;
    } else
        vbuf->vbuf_type = MONAD_FIBER_VBUF_IN_PLACE;
}

static inline struct iovec monad_fiber_vbuf_data(monad_fiber_vbuf_t *vbuf) {
    struct iovec iov;
    if (vbuf->vbuf_type == MONAD_FIBER_VBUF_EXTERNAL)
        return vbuf->external_buf;
    iov.iov_base = vbuf->in_place;
    iov.iov_len = sizeof vbuf->in_place;
    return iov;
}

#ifdef __cplusplus
} // extern "C"
#endif
