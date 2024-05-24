#pragma once

#include <monad/fiber/channel.h>
#include <monad/fiber/context.h>
#include <monad/fiber/current.h>
#include <monad/fiber/task.h>

#include <pthread.h>

#if defined(__cplusplus)
    #include <atomic>
using std::atomic_bool;
using std::atomic_int;

extern "C"
{
#else
    #include <stdatomic.h>

#endif

#include <setjmp.h>
#include <stddef.h>

typedef struct monad_fiber_pooled
{
    monad_fiber_t fiber;
    monad_fiber_task_t *current_task;
    bool idle;
    jmp_buf exit_jmp;
    struct monad_fiber_pool *pool;
} monad_fiber_pooled_t;

typedef struct monad_fiber_pooled monad_fiber_pooled_t;

/*typedef struct monad_fiber
{
  monad_fiber_task_t self_task;
  monad_fiber_context_t * context;
  monad_fiber_pool_t * pool;
  atomic_bool shall_resume, busy;
  jmp_buf jump_to_exit;

  monad_fiber_task_t  * current_task;
  size_t                current_priority;

} monad_fiber_t;*/

typedef struct monad_fiber_pool
{
    monad_fiber_pooled_t *fibers_data;
    size_t fibers_size;

    monad_fiber_task_queue_t queue;
    monad_fiber_channel_t queue_semaphore;
    pthread_mutex_t queue_mutex;

    atomic_int fiber_id_source; // if this is zero we're stopping

} monad_fiber_pool_t;

void monad_fiber_pool_create(monad_fiber_pool_t *, size_t fiber);
void monad_fiber_pool_destroy(monad_fiber_pool_t *);
void monad_fiber_pool_run(
    monad_fiber_pool_t *, monad_fiber_task_t *task, int64_t priority);

#if defined(__cplusplus)
}
#endif
