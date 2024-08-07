#pragma once

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct monad_fiber monad_fiber_t;
typedef struct monad_run_queue monad_run_queue_t;

/// Create a fiber run queue of the specified fixed size; this is a priority
/// queue of fibers, ordered by priority
int monad_run_queue_create(size_t capacity, monad_run_queue_t **rq);

/// Destroys a fiber run queue; destruction is not thread safe, so all push and
/// pop operations must be finished
void monad_run_queue_destroy(monad_run_queue_t *rq);

/// Push a fiber onto the priority queue; returns ENOBUFS is there is
/// insufficient space in the queue
int monad_run_queue_push(monad_run_queue_t *rq, monad_fiber_t *fiber);

/// Pop the highest priority fiber from the queue; returns nullptr if the
/// queue is empty
monad_fiber_t *monad_run_queue_pop(monad_run_queue_t *rq);

#ifdef __cplusplus
} // extern "C"
#endif
