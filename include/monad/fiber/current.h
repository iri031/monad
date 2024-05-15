#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

#include "context.h"
#include "scheduler.h"

typedef struct monad_fiber
{
    monad_fiber_task_t task;
    monad_fiber_context_t *context;
    int64_t priority;
    monad_fiber_scheduler_t *scheduler;
} monad_fiber_t;

monad_fiber_t *monad_fiber_current();
bool monad_fiber_is_main(monad_fiber_t *const);

// switch manually, without scheduling anything.
void monad_fiber_switch_to_fiber(monad_fiber_t *);
void monad_fiber_switch_to_main();

void monad_fiber_init_main();

// give up control IF something with higher priority is scheduled, but mark the
// current for resumption
void monad_fiber_yield();
void monad_fiber_yield_to(monad_fiber_context_t *target);
monad_fiber_t *monad_fiber_activate_fiber(monad_fiber_t *new_current);

monad_fiber_t *monad_fiber_main();

void monad_fiber_await(
    void (*suspend_to)(monad_fiber_t * /*task */, void * /*arg*/), void *arg);

#ifdef __cplusplus
}
#endif
