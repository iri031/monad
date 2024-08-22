#include <errno.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

int monad_run_queue_create(size_t capacity, monad_run_queue_t **rq)
{
    static_assert(alignof(monad_run_queue_t) >= alignof(monad_run_queue_t *));
    monad_run_queue_t *run_queue;
    size_t const total_size =
        sizeof *run_queue + capacity * sizeof(monad_fiber_t *);
    if (rq == nullptr) {
        return EFAULT;
    }
    *rq = run_queue = (monad_run_queue_t *)malloc(total_size);
    if (run_queue == nullptr) {
        return errno;
    }
    memset((void *)run_queue, 0, sizeof *run_queue);
    monad_spinlock_init(&run_queue->lock);
    run_queue->fibers = (monad_fiber_t **)(run_queue + 1);
    atomic_init(&run_queue->size, 0);
    run_queue->capacity = capacity;
    return 0;
}

void monad_run_queue_destroy(monad_run_queue_t *rq)
{
    MONAD_ASSERT(rq != nullptr);
    free(rq);
}
