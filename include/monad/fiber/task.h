#pragma once

#include <stddef.h>

typedef struct monad_fiber_task
{
    void (*resume)(struct monad_fiber_task *const);
    void (*destroy)(struct monad_fiber_task *const);
} monad_fiber_task_t;

struct monad_fiber_task_node
{
    monad_fiber_task_t *task;
    size_t priority;
};

typedef struct monad_fiber_task_queue
{

    // ring buffer. not lock free.
    struct monad_fiber_task_node *memory;
    size_t capacity;
    struct monad_fiber_task_node *data;
    size_t size;
} monad_fiber_task_queue_t;

void monad_fiber_task_queue_init(struct monad_fiber_task_queue *);
void monad_fiber_task_queue_destroy(struct monad_fiber_task_queue *);
void monad_fiber_task_queue_grow(struct monad_fiber_task_queue *);
struct monad_fiber_task_node
monad_fiber_task_queue_pop_front(struct monad_fiber_task_queue *);
void monad_fiber_task_queue_insert(
    struct monad_fiber_task_queue *, monad_fiber_task_t *task, size_t priority);
