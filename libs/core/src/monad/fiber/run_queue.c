#include <errno.h>
#include <stdlib.h>
#include <string.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

/// A priority queue, implemented using a min-heap; used to pick the highest
/// priority fiber to schedule next. For reference, see
/// [CLRS 6.5: Priority Queues]
struct monad_run_queue {
    alignas(64) spinlock_t lock;
    monad_fiber_t **fibers;
    size_t size;
    size_t capacity;
};

#define PQ_PARENT_IDX(i) ((i - 1) / 2)
#define PQ_LEFT_CHILD_IDX(i) (2*i + 1)
#define PQ_RIGHT_CHILD_IDX(i) (2*i + 2)

static inline void swap_ptr(monad_fiber_t **p1, monad_fiber_t **p2) {
    monad_fiber_t *const t = *p2;
    *p2 = *p1;
    *p1 = t;
}

static inline void prio_queue_min_heapify(struct monad_run_queue *rq,
                                          size_t parent_idx) {
HeapifyNextLevel:
    size_t smallest_idx = parent_idx;
    size_t left_idx = PQ_LEFT_CHILD_IDX(parent_idx);
    size_t right_idx = PQ_RIGHT_CHILD_IDX(parent_idx);

    if (left_idx < rq->size &&
        rq->fibers[left_idx]->priority < rq->fibers[smallest_idx]->priority)
        smallest_idx = left_idx;

    if (right_idx < rq->size &&
        rq->fibers[right_idx]->priority < rq->fibers[smallest_idx]->priority)
        smallest_idx = right_idx;

    if (smallest_idx == parent_idx)
        return;

    swap_ptr(&rq->fibers[parent_idx], &rq->fibers[smallest_idx]);
    parent_idx = smallest_idx;
    goto HeapifyNextLevel;
}

int monad_run_queue_create(size_t capacity, monad_run_queue_t **rq) {
    monad_run_queue_t *run_queue;
    if (rq == nullptr)
        return EFAULT;
    *rq = run_queue = malloc(sizeof **rq + capacity * sizeof(monad_fiber_t*));
    if (run_queue == nullptr)
        return errno;
    memset(run_queue, 0, sizeof *run_queue);
    spinlock_init(&run_queue->lock);
    run_queue->fibers = (monad_fiber_t**)(run_queue + 1);
    run_queue->capacity = capacity;
    return 0;
}

void monad_run_queue_destroy(monad_run_queue_t *rq) {
    MONAD_ASSERT(rq != nullptr);
    free(rq);
}

int monad_run_queue_push(monad_run_queue_t *rq, monad_fiber_t *fiber) {
    size_t idx;
    MONAD_ASSERT(rq != nullptr && fiber != nullptr);
    spinlock_lock(&rq->lock);
    if (rq->size == rq->capacity) {
        spinlock_unlock(&rq->lock);
        return ENOBUFS;
    }
    fiber->run_queue = rq;
    idx = rq->size++;
    rq->fibers[idx] = fiber;
    while (idx != 0 &&
           rq->fibers[idx]->priority < rq->fibers[PQ_PARENT_IDX(idx)]->priority)
    {
        swap_ptr(&rq->fibers[idx], &rq->fibers[PQ_PARENT_IDX(idx)]);
        idx = PQ_PARENT_IDX(idx);
    }
    spinlock_unlock(&rq->lock);
    return 0;
}

monad_fiber_t *monad_run_queue_pop(monad_run_queue_t *rq) {
    monad_fiber_t *min_prio_fiber;
    MONAD_ASSERT(rq != nullptr);
    spinlock_lock(&rq->lock);
    if (rq->size == 0) {
        spinlock_unlock(&rq->lock);
        return nullptr;
    }
    min_prio_fiber = rq->fibers[0];
    --rq->size;
    if (rq->size > 0) {
        swap_ptr(&rq->fibers[0], &rq->fibers[rq->size]);
        prio_queue_min_heapify(rq, 0);
    }
    spinlock_unlock(&rq->lock);
    return min_prio_fiber;
}