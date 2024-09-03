#pragma once

#include <monad/core/assert.h>
#include <monad/core/cpu_relax.h>
#include <monad/core/likely.h>
#include <monad/core/thread.h>

#if MONAD_SPINLOCK_TRACK_OWNER_INFO
    #include <monad/core/srcloc.h>
#endif

#include <assert.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static_assert(ATOMIC_LONG_LOCK_FREE == 2);

typedef atomic_long spinlock_t;
typedef struct monad_spinlock monad_spinlock_t;

#if MONAD_SPINLOCK_TRACK_STATS_ATOMIC
typedef atomic_ulong monad_spinstat_t;
    #define MONAD_SPINSTAT_INC(X) atomic_fetch_add(&(X), 1)
#else
typedef unsigned long monad_spinstat_t;
    #define MONAD_SPINSTAT_INC(X) ++(X)
#endif

// TODO(ken): remove this workaround when we have clang-19
#if defined(__clang__) && __clang_major__ < 19
    #define MONAD_SPINLOCK_HIST_BUCKETS 15
#else
constexpr size_t MONAD_SPINLOCK_HIST_BUCKETS = 15;
#endif

/// Lock statistics; these may not be 100% accurate, since we may not be
/// atomically incrementing them (some data could be lost)
struct monad_spinlock_stats
{
    monad_spinstat_t total_try_locks;      ///< # times try_lock is called
    monad_spinstat_t total_try_lock_fail;  ///< # times try_locked failed
    monad_spinstat_t total_locks;          ///< # times lock is called
    monad_spinstat_t total_lock_init_fail; ///< # times lock needed > 1 try
    monad_spinstat_t
        tries_histogram[MONAD_SPINLOCK_HIST_BUCKETS + 1]; /// lock tries histo
};

struct monad_spinlock
{
    atomic_long owner_tid;             ///< System ID of thread that owns lock
#if MONAD_SPINLOCK_TRACK_STATS
    struct monad_spinlock_stats stats; ///< Lock contention stats
#endif
#if MONAD_SPINLOCK_TRACK_OWNER_INFO
    monad_source_location_t srcloc;    ///< Location in code where lock taken
#endif
};

static inline bool monad_spinlock_is_owned(monad_spinlock_t *const lock)
{
    return atomic_load_explicit(&lock->owner_tid, memory_order_acquire) ==
           monad_thread_get_id();
}

static inline bool monad_spinlock_is_unowned(monad_spinlock_t *const lock)
{
    return atomic_load_explicit(&lock->owner_tid, memory_order_acquire) == 0;
}

static inline void monad_spinlock_init(monad_spinlock_t *const lock)
{
    atomic_init(&lock->owner_tid, 0);
#if MONAD_SPINLOCK_TRACK_OWNER_INFO
    memset(&lock->srcloc, 0, sizeof lock->srcloc);
#endif
#if MONAD_SPINLOCK_TRACK_STATS
    #ifdef __cplusplus
    new (&lock->stats) monad_spinlock_stats{};
    #else
    memset(&lock->stats, 0, sizeof lock->stats);
    #endif
#endif
}

static inline bool monad_spinlock_try_lock(monad_spinlock_t *const lock)
{
    monad_tid_t expected = 0;
    monad_tid_t const desired = monad_thread_get_id();
    bool const is_locked = atomic_compare_exchange_weak_explicit(
        &lock->owner_tid,
        &expected,
        desired,
        memory_order_acquire,
        memory_order_relaxed);
#if MONAD_SPINLOCK_TRACK_STATS
    MONAD_SPINSTAT_INC(lock->stats.total_try_locks);
    if (MONAD_UNLIKELY(!is_locked)) {
        MONAD_SPINSTAT_INC(lock->stats.total_try_lock_fail);
    }
#endif
    return is_locked;
}

static inline void monad_spinlock_lock(monad_spinlock_t *const lock)
{
    monad_tid_t const desired = monad_thread_get_id();
    monad_tid_t expected;
    [[maybe_unused]] unsigned long tries = 0;
    [[maybe_unused]] unsigned histo_bucket;
    bool owned;

    MONAD_DEBUG_ASSERT(!monad_spinlock_is_owned(lock));
    do {
        /**
         * TODO further analysis of retry logic
         * - if weak cmpxch fails, spin again or cpu relax?
         * - compare intel vs arm
         * - benchmark with real use cases
         */
        unsigned retries = 0;
        while (MONAD_UNLIKELY(
            atomic_load_explicit(&lock->owner_tid, memory_order_relaxed))) {
            if (MONAD_LIKELY(retries < 128)) {
                ++retries;
            }
            else {
                cpu_relax();
            }
        }
        expected = 0;
#if MONAD_SPINLOCK_TRACK_STATS
        ++tries;
#endif
        owned = atomic_compare_exchange_weak_explicit(
            &lock->owner_tid,
            &expected,
            desired,
            memory_order_acquire,
            memory_order_relaxed);
    }
    while (MONAD_UNLIKELY(!owned));

#if MONAD_SPINLOCK_TRACK_STATS
    MONAD_SPINSTAT_INC(lock->stats.total_locks);
    if (MONAD_LIKELY(tries > 1)) {
        MONAD_SPINSTAT_INC(lock->stats.total_lock_init_fail);
    }
    histo_bucket = stdc_bit_width(tries - 1);
    if (MONAD_UNLIKELY(histo_bucket >= MONAD_SPINLOCK_HIST_BUCKETS)) {
        histo_bucket = MONAD_SPINLOCK_HIST_BUCKETS;
    }
    MONAD_SPINSTAT_INC(lock->stats.tries_histogram[histo_bucket]);
#endif
}

static inline void monad_spinlock_unlock(monad_spinlock_t *const lock)
{
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(lock));
    atomic_store_explicit(&lock->owner_tid, 0, memory_order_release);
}

#if MONAD_SPINLOCK_TRACK_OWNER_INFO
static inline bool monad_spinlock_try_lock_with_srcloc(
    monad_spinlock_t *const lock, monad_source_location_t srcloc)
{
    bool const have_lock = monad_spinlock_try_lock(lock);
    if (have_lock) {
        lock->srcloc = srcloc;
    }
    return have_lock;
}

static inline void monad_spinlock_lock_with_srcloc(
    monad_spinlock_t *const lock, monad_source_location_t srcloc)
{
    monad_spinlock_lock(lock);
    lock->srcloc = srcloc;
}

    #define MONAD_SPINLOCK_TRY_LOCK(LCK)                                       \
        monad_spinlock_try_lock_with_srcloc(                                   \
            (LCK),                                                             \
            (monad_source_location_t){                                         \
                __PRETTY_FUNCTION__, __FILE__, __LINE__, 0})

    #define MONAD_SPINLOCK_LOCK(LCK)                                           \
        monad_spinlock_lock_with_srcloc(                                       \
            (LCK),                                                             \
            (monad_source_location_t){                                         \
                __PRETTY_FUNCTION__, __FILE__, __LINE__, 0})
#else

    #define MONAD_SPINLOCK_TRY_LOCK(LCK) monad_spinlock_try_lock((LCK))
    #define MONAD_SPINLOCK_LOCK(LCK) monad_spinlock_lock((LCK))

#endif

#define MONAD_SPINLOCK_UNLOCK(LCK) monad_spinlock_unlock((LCK))
