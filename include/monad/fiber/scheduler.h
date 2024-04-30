#pragma once

#include "task.h"

#if defined(__cplusplus)
    #include <atomic>
using std::atomic_int;

extern "C"
{
#else
    #include <stdatomic.h>

#endif

#include <pthread.h>

#include <assert.h>
#include <errno.h>
#include <malloc.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

typedef struct monad_fiber_scheduler
{
    pthread_t *threads;
    size_t thread_count;
    pthread_mutex_t mutex;
    pthread_cond_t cond;

    monad_fiber_task_queue_t task_queue;
    atomic_int thread_id_source; // if this is zero we're stoppping
} monad_fiber_scheduler_t;

monad_fiber_scheduler_t *monad_fiber_scheduler_current();

void monad_fiber_scheduler_work(monad_fiber_scheduler_t *);
void monad_fiber_scheduler_create(monad_fiber_scheduler_t *, size_t threads);
void monad_fiber_scheduler_destroy(monad_fiber_scheduler_t *);
void monad_fiber_scheduler_stop(monad_fiber_scheduler_t *);

void monad_fiber_scheduler_post(
    monad_fiber_scheduler_t *, monad_fiber_task_t *task, size_t priority);
void monad_fiber_scheduler_dispatch(
    monad_fiber_scheduler_t *, monad_fiber_task_t *task, size_t priority);

monad_fiber_task_t *monad_fiber_scheduler_pop_higher_priority_task(
    monad_fiber_scheduler_t *, size_t priority);

#if defined(__cplusplus)
}
#endif
