#include <errno.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include <monad/core/assert.h>
#include <monad/core/dump.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

int monad_run_queue_create(size_t capacity, monad_run_queue_t **rq) {
    static_assert(alignof(monad_run_queue_t) >= alignof(monad_run_queue_t*));
    monad_run_queue_t *run_queue;
    const size_t total_size = sizeof *run_queue +
                              capacity * sizeof(monad_fiber_t*);
    if (rq == nullptr)
        return EFAULT;
    *rq = run_queue = (monad_run_queue_t *)malloc(total_size);
    if (run_queue == nullptr)
        return errno;
    memset((void *)run_queue, 0, sizeof *run_queue);
    monad_spinlock_init(&run_queue->lock);
    run_queue->fibers = (monad_fiber_t**)(run_queue + 1);
    run_queue->capacity = capacity;
    return 0;
}

void monad_run_queue_destroy(monad_run_queue_t *rq) {
    MONAD_ASSERT(rq != nullptr);
    free(rq);
}

void monad_run_queue_dump_stats(const monad_run_queue_t *rq,
                                monad_dump_ctx_t *stats_ctx) {
    stats_ctx->max_field_length = sizeof "push lock fail" - 1;
#define STATS_WF(...) monad_dump_printf_field(stats_ctx, __VA_ARGS__)
    STATS_WF("push", "%zu", rq->stats.total_push);
    STATS_WF("push lock fail", "%zu (%.2f)",rq->stats.total_push_lock_fail,
             (float)rq->stats.total_push_lock_fail /
                 (float)rq->stats.total_push);
    STATS_WF("pop", "%zu", rq->stats.total_pop);
    STATS_WF("pop lock fail", "%zu (%.2f)", rq->stats.total_pop_lock_fail,
             (float)rq->stats.total_pop_lock_fail / (float)rq->stats.total_pop);
    STATS_WF("pop empty", "%zu (%.2f)", rq->stats.total_pop_empty,
             (float)rq->stats.total_pop_empty / (float)rq->stats.total_pop);
#undef STATS_WF
}