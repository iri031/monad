#pragma once

#include <errno.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>

#ifdef __cplusplus
extern "C" {
#endif

//#define MONAD_CORE_RUN_QUEUE_NO_MIGRATE 1

struct monad_run_queue_stats;
typedef struct monad_run_queue monad_run_queue_t;

/// Create a fiber run queue of the specified fixed size; this is a priority
/// queue of fibers, ordered by the monad_fiber_t scheduling "priority" field
int monad_run_queue_create(size_t capacity, monad_run_queue_t **rq);

/// Destroys a fiber run queue; destruction is not thread safe, so all push and
/// pop operations must be finished
void monad_run_queue_destroy(monad_run_queue_t *rq);

/// Try to push a fiber onto the priority queue; this is non-blocking and
/// returns ENOBUFS immediately is there is insufficient space in the queue
static inline int monad_run_queue_try_push(monad_run_queue_t *rq,
                                           monad_fiber_t *fiber);

/// Try to pop the highest priority fiber from the queue; this is non-blocking
/// and returns nullptr if the queue is empty, otherwise it returns a locked
/// fiber
static inline monad_fiber_t *monad_run_queue_try_pop(monad_run_queue_t *rq);

/// Returns true if the run queue is currently empty;be aware that this has
/// a TOCTOU race in multithreaded code, e.g., this could change asynchronously
/// because of another thread
static inline bool monad_run_queue_is_empty(const monad_run_queue_t *rq);

/// Scheduling statistics; some writes to these are unlocked without the use
/// of fetch_add atomic semantics, so they are only approximate
struct monad_run_queue_stats {
    size_t total_pop;              ///< # of times caller tried to pop a fiber
    size_t total_pop_empty;        ///< # of times there was no fiber in queue
    size_t total_push;             ///< # of times caller tried to push a fiber
    size_t total_push_full;        ///< # of times fiber queue was full
    size_t total_push_not_ready;   ///< # of times pushed fiber unready
};

/// A priority queue, implemented using a min-heap; used to pick the highest
/// priority fiber to schedule next. For reference, see
/// [CLRS 6.5: Priority Queues]
struct monad_run_queue {
    alignas(64) monad_spinlock_t lock;
    monad_fiber_t **fibers;
    size_t capacity;
    alignas(64) atomic_size_t size;
    alignas(64) struct monad_run_queue_stats stats;
};

#define PQ_PARENT_IDX(i) ((i - 1) / 2)
#define PQ_LEFT_CHILD_IDX(i) (2*i + 1)
#define PQ_RIGHT_CHILD_IDX(i) (2*i + 2)

static inline void _monad_fiber_ptr_swap(const monad_fiber_t **p1,
                                         const monad_fiber_t **p2) {
    const monad_fiber_t *const t = *p2;
    *p2 = *p1;
    *p1 = t;
}

static inline unsigned prio_queue_min_heapify(const monad_fiber_t **fibers,
                                              size_t queue_size,
                                              size_t parent_idx) {
    unsigned iters = 1;
HeapifyNextLevel:
    size_t smallest_idx = parent_idx;
    size_t left_idx = PQ_LEFT_CHILD_IDX(parent_idx);
    size_t right_idx = PQ_RIGHT_CHILD_IDX(parent_idx);

    if (left_idx < queue_size &&
        fibers[left_idx]->priority < fibers[smallest_idx]->priority)
        smallest_idx = left_idx;

    if (right_idx < queue_size &&
        fibers[right_idx]->priority < fibers[smallest_idx]->priority)
        smallest_idx = right_idx;

    if (smallest_idx == parent_idx)
        return iters;

    _monad_fiber_ptr_swap(&fibers[parent_idx], &fibers[smallest_idx]);
    parent_idx = smallest_idx;
    ++iters;
    goto HeapifyNextLevel;
}

static inline int monad_run_queue_try_push(monad_run_queue_t *rq,
                                           monad_fiber_t *fiber) {
    size_t idx;
    size_t size;
    int rc = 0;
    unsigned heapify_iters = 0;

    MONAD_DEBUG_ASSERT(rq != nullptr && fiber != nullptr);
    MONAD_SPINLOCK_LOCK(&rq->lock);
    ++rq->stats.total_push;
    // Relaxed because it isn't ordered before the spinlock acquisition
    size = atomic_load_explicit(&rq->size, memory_order_relaxed);
    if (MONAD_UNLIKELY(size == rq->capacity)) {
        ++rq->stats.total_push_full;
        rc = ENOBUFS;
        goto Finish;
    }

    if (MONAD_UNLIKELY(!monad_spinlock_is_owned(&fiber->lock)))
        MONAD_SPINLOCK_LOCK(&fiber->lock);
    if (MONAD_UNLIKELY(fiber->state != MF_STATE_CAN_RUN)) {
        monad_spinlock_unlock(&fiber->lock);
        ++rq->stats.total_push_not_ready;
        rc = EBUSY;
        goto Finish;
    }

    idx = size++;
    rq->fibers[idx] = fiber;
    while (idx != 0 &&
           rq->fibers[idx]->priority < rq->fibers[PQ_PARENT_IDX(idx)]->priority)
    {
        _monad_fiber_ptr_swap((const monad_fiber_t**)&rq->fibers[idx],
                              (const monad_fiber_t**)&rq->fibers[PQ_PARENT_IDX(idx)]);
        idx = PQ_PARENT_IDX(idx);
        ++heapify_iters;
    }
    fiber->run_queue = rq;
    fiber->state = MF_STATE_RUN_QUEUE;
    monad_spinlock_unlock(&fiber->lock);
    atomic_store_explicit(&rq->size, size, memory_order_relaxed);
Finish:
    monad_spinlock_unlock(&rq->lock);
    (void)heapify_iters;
    return rc;
}

static inline monad_fiber_t *monad_run_queue_try_pop(monad_run_queue_t *rq) {
    monad_fiber_t *min_prio_fiber;
    size_t size;
    unsigned heapify_iter;

    MONAD_DEBUG_ASSERT(rq != nullptr);
    ++rq->stats.total_pop;
    // Because we're I/O bound, the run_queue is usually empty (we're often
    // waiting for any fiber to become runnable again). To prevent constant lock
    // contention, the queue size is atomic and we can poll it
    size = atomic_load_explicit(&rq->size, memory_order_acquire);
    if (MONAD_UNLIKELY(size == 0)) {
        ++rq->stats.total_pop_empty;
        return nullptr;
    }
    if (MONAD_UNLIKELY(!MONAD_SPINLOCK_TRY_LOCK(&rq->lock))) {
        ++rq->stats.total_pop_empty;
        // We failed to get the lock; the likeliest sequence of events is that
        // we had multiple pollers and only one fiber became available. By
        // failing to get the lock, we likely would fail completely (the size
        // will probably be zero soon)
        return nullptr;
    }
    // The size may have changed in between our polling of the size and getting
    // the lock that protects writes to it; the load is relaxed here since we
    // piggy-back off the memory ordering imposed by the spinlock
    size = atomic_load_explicit(&rq->size, memory_order_relaxed);
    if (MONAD_UNLIKELY(size == 0)) {
        ++rq->stats.total_pop_empty;
        monad_spinlock_unlock(&rq->lock);
        return nullptr;
    }

    min_prio_fiber = rq->fibers[0];

#if MONAD_CORE_RUN_QUEUE_NO_MIGRATE
    if (min_prio_fiber->last_thread != 0 &&
        min_prio_fiber->last_thread != pthread_self()) {
        monad_spinlock_unlock(&rq->lock);
        return nullptr;
    }
#endif

    --size;
    atomic_store_explicit(&rq->size, size, memory_order_release);
    if (MONAD_LIKELY(size > 0)) {
        _monad_fiber_ptr_swap((const monad_fiber_t**)&rq->fibers[0],
                              (const monad_fiber_t**)&rq->fibers[size]);
        heapify_iter = prio_queue_min_heapify((const monad_fiber_t**)rq->fibers,
                                              size, 0);
    }
    monad_spinlock_unlock(&rq->lock);
    (void)heapify_iter; // XXX: make a histogram of iter count?

    // Return the fiber in a locked state; the caller is almost certainly going
    // to call monad_fiber_run immediately
    MONAD_SPINLOCK_LOCK(&min_prio_fiber->lock);
    min_prio_fiber->state = MF_STATE_CAN_RUN;
    return min_prio_fiber;
}

#undef PQ_PARENT_IDX
#undef PQ_LEFT_CHILD_IDX
#undef PQ_RIGHT_CHILD_IDX

static inline bool monad_run_queue_is_empty(const monad_run_queue_t *rq) {
    return atomic_load_explicit(&rq->size, memory_order_relaxed) == 0;
}

#ifdef __cplusplus
} // extern "C"
#endif
