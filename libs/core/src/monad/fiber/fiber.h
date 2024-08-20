#pragma once

/**
 * @file
 *
 * This file defines the interface for our lightweight fiber library
 */

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct monad_fiber monad_fiber_t;
typedef struct monad_fiber_stack monad_fiber_stack_t;
typedef struct monad_fiber_suspend_info monad_fiber_suspend_info_t;

typedef uintptr_t (monad_fiber_ffunc_t)(uintptr_t);
typedef int64_t monad_fiber_prio_t;

// TODO(ken): https://github.com/monad-crypto/monad-internal/issues/498
static monad_fiber_prio_t const MONAD_FIBER_PRIO_HIGHEST = INT64_MIN;
static monad_fiber_prio_t const MONAD_FIBER_PRIO_LOWEST = INT64_MAX - 1;
static monad_fiber_prio_t const MONAD_FIBER_PRIO_NO_CHANGE = INT64_MAX;

enum monad_fiber_suspend_type : unsigned
{
    MF_SUSPEND_NONE,
    MF_SUSPEND_YIELD,
    MF_SUSPEND_SLEEP,
    MF_SUSPEND_RETURN
};

/// When a fiber is suspended, monad_fiber_run will fill out one of these
/// structures to describe the reason for the suspension
struct monad_fiber_suspend_info
{
    enum monad_fiber_suspend_type suspend_type; ///< Reason for last suspension
    uintptr_t eval;                             ///< Value (for YIELD / RETURN)
};

/*
 * Public interface: functions that are called by users of the library
 */

/// Initialize a fiber, given a description of its stack area
void monad_fiber_init(monad_fiber_t *fiber, monad_fiber_stack_t stack);

/// Set the function that the fiber will run; this may be called multiple times,
/// to reuse the fiber's resources (e.g., its stack) to run new functions
int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, uintptr_t fdata);

/// Returns the structure representing the currently executing fiber
monad_fiber_t *monad_fiber_self();

/// Begin running a fiber's function, or resume that function at the suspension
/// point, if it was suspended; this call returns the next time the function
/// suspends, and populates @ref suspend_info with info about that suspension
int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info);

/// Similar to sched_yield(2) or pthread_yield_np(3), but for fibers: yields
/// from the currently-running fiber back to the previously-running fiber
void monad_fiber_yield(uintptr_t eval);

struct monad_fiber_stack
{
    void *stack_base;   ///< Lowest addr, incl. unusable memory (guard pages)
    void *stack_bottom; ///< Bottom of usable stack
    void *stack_top;    ///< Top of usable stack
};

struct monad_fiber
{
    monad_fiber_prio_t priority; ///< Scheduling priority
};

#if __cplusplus
} // extern "C"
#endif
