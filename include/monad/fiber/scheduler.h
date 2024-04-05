#pragma once


#if defined(__cplusplus)
#include <atomic>
using std::atomic_int;

extern "C" {
#else
#include <stdatomic.h>

#endif

#define MONAD_ASSERT(Expression) assert(Expression)
#define MONAD_CCALL_ASSERT(Expression) {int _return_value_ = Expression; MONAD_ASSERT(!_return_value_); }

#define _GNU_SOURCE
#include <pthread.h>

#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <malloc.h>

typedef struct monad_fiber_scheduler_task
{
  void (*resume) (struct monad_fiber_scheduler_task* const);
  void (*destroy)(struct monad_fiber_scheduler_task* const);
} monad_fiber_scheduler_task_t;


struct monad_fiber_scheduler_task_node {
  monad_fiber_scheduler_task_t * task;
  size_t priority;
};


struct monad_fiber_scheduler_task_queue {

  // ring buffer. not lock free.
  struct monad_fiber_scheduler_task_node * memory;
  size_t capacity;
  struct monad_fiber_scheduler_task_node * data;
  size_t size;
};

typedef struct monad_fiber_scheduler
{
  pthread_t *threads;
  size_t thread_count;
  pthread_mutex_t mutex;
  pthread_cond_t cond;

  struct monad_fiber_scheduler_task_queue task_queue;
  atomic_int thread_id_source; // if this is zero we're stoppping
} monad_fiber_scheduler_t;


monad_fiber_scheduler_t * monad_fiber_scheduler_current();

void monad_fiber_scheduler_work    (monad_fiber_scheduler_t *);
void monad_fiber_scheduler_create  (monad_fiber_scheduler_t *, size_t threads);
void monad_fiber_scheduler_destroy (monad_fiber_scheduler_t *);
void monad_fiber_scheduler_stop    (monad_fiber_scheduler_t *);
void monad_fiber_scheduler_post    (monad_fiber_scheduler_t *, monad_fiber_scheduler_task_t * task, size_t priority);
void monad_fiber_scheduler_dispatch(monad_fiber_scheduler_t *, monad_fiber_scheduler_task_t * task, size_t priority);


#if defined(__cplusplus)
}
#endif