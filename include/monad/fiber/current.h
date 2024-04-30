#pragma once

#include "context.h"
#include "scheduler.h"

typedef struct monad_fiber
{
    monad_fiber_task_t task;
    monad_fiber_context_t *context;
    size_t priority;
    monad_fiber_scheduler_t *scheduler;
} monad_fiber_t;

monad_fiber_t *monad_fiber_current();
bool monad_fiber_is_main(monad_fiber_t *const);

// switch manually, without scheduling anything.
void monad_fiber_switch_to_fiber(monad_fiber_t *);
void monad_fiber_switch_to_main();

// give up control IF something with higher priority is scheduled, but mark the
// current for resumption
void monad_fiber_yield();
void monad_fiber_yield_to(monad_fiber_context_t *target);

monad_fiber_t *monad_fiber_main();

void monad_fiber_await(
    void (*suspend_to)(monad_fiber_t * /*task */, void * /*arg*/), void *arg);
