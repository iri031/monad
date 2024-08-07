#pragma once

/**
 * @file
 *
 * This file defines the interface for our lightweight fiber library
 */

#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/queue.h>
#include <monad/core/spinlock.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef void *monad_fiber_ctx_t;
typedef struct monad_fiber monad_fiber_t;
typedef struct monad_fiber_status monad_fiber_status_t;
typedef struct monad_fiber_stack monad_fiber_stack_t;
typedef struct monad_run_queue monad_run_queue_t;

typedef TAILQ_HEAD(monad_fiber_wait_queue, monad_fiber)
    monad_fiber_wait_queue_t;

typedef uintptr_t (monad_fiber_ffunc_t)(uintptr_t);
typedef int64_t monad_fiber_prio_t;

constexpr monad_fiber_prio_t MONAD_FIBER_PRIO_HIGHEST = INT64_MIN;
constexpr monad_fiber_prio_t MONAD_FIBER_PRIO_LOWEST = INT64_MAX - 1;
constexpr monad_fiber_prio_t MONAD_FIBER_PRIO_NO_CHANGE = INT64_MAX;

enum monad_fiber_state {
    MONAD_FIBER_INIT,          ///< Fiber function not run yet
    MONAD_FIBER_YIELD,         ///< Suspended by monad_fiber_yield
    MONAD_FIBER_SLEEP,         ///< Asleep on a wait queue
    MONAD_FIBER_SPIN_WAIT,     ///< Used by "thread fibers", see fiber_thr.c
    MONAD_FIBER_RUN,           ///< Fiber is running
    MONAD_FIBER_RETURN         ///< Suspended by fiber function return; finished
};

struct monad_fiber_status {
    enum monad_fiber_state state; ///< Defines run/suspend/wait state for fiber
    uintptr_t eval;               ///< Integer code for YIELD / RETURN states
};

/*
 * Public interface: functions that are called by users of the library
 */

/// Initialize the fiber, given a description of its stack area
void monad_fiber_init(monad_fiber_t *fiber, monad_fiber_stack_t stack);

/// Set the function that will run on a fiber; this may be called many times,
/// to reuse the fiber's resources (e.g., its stack) to run new functions
monad_fiber_t*
monad_fiber_set_function(monad_fiber_t *fiber, monad_fiber_prio_t priority,
                         monad_fiber_ffunc_t *ffunc, uintptr_t fdata);

/// Returns the structure representing the currently executing fiber
monad_fiber_t *monad_fiber_self();

/// Begin running a new fiber (or resume that fiber at the suspension point,
/// if it's suspended); this function returns when the fiber suspends
monad_fiber_status_t monad_fiber_run(monad_fiber_t *fiber);

/// Yield from the current fiber back to the previously executing fiber
void monad_fiber_yield(uintptr_t eval);

/// Determine if the given fiber is a thread fiber; see fiber_thr.c for an
/// explanation of thread fibers
static inline bool monad_fiber_is_thread_fiber(const monad_fiber_t *fiber);

struct monad_fiber_stack {
    void *stack_base;    ///< Lowest addr, incl. unusable memory (guard pages)
    void *stack_bottom;  ///< Bottom of usable stack
    void *stack_top;     ///< Top of usable stack
};

struct monad_fiber_stats {
    size_t total_reset;   ///< # of times monad_fiber_set_function is called
    size_t total_run;     ///< # of times fiber has been run (resumed)
    size_t total_sleep;   ///< # of times monad_fiber_sleep was called
    size_t total_migrate; ///< # of times fiber has moved between threads
};

struct monad_fiber {
    monad_fiber_prio_t priority;           ///< Scheduling priority of fiber
    monad_fiber_status_t status;           ///< Last updated run state
    monad_fiber_wait_queue_t *wait_queue;  ///< Last wait queue we slept on
    TAILQ_ENTRY(monad_fiber) wait_link;    ///< Linkage for wait_queue
    TAILQ_ENTRY(monad_fiber) fiber_link;   ///< For crash dump "all fibers" list
    union
    {
        monad_run_queue_t *run_queue;      ///< Last run queue that scheduled us
        void *thread_fiber_state;          ///< Book-keeping for a thread fiber
    };
    monad_fiber_ctx_t fctx;                ///< Suspended context of this fiber
    monad_fiber_t *prev_fiber;             ///< Previously active fiber
    pthread_t last_thread;                 ///< For debug: last thread we ran on
    int last_thread_id;                    ///< For debug: system ID of last thr
    struct monad_fiber_stats stats;        ///< Statistics about this fiber
    monad_fiber_ffunc_t *ffunc;            ///< Fiber function to run
    uintptr_t fdata;                       ///< Opaque user data passed to ffunc
    monad_fiber_stack_t stack;             ///< Range of our stack
#if MONAD_HAVE_ASAN
    void *fake_stack_save;                 ///< For ASAN fiber support
#endif
};

/*
 * Private interface: these functions are only called internally, by the
 * synchronization primitives (e.g., monad_fiber_channel_t,
 * monad_fiber_semaphore_t, etc.)
 */

/// Put the current fiber to sleep on the given wait queue, to be woken up
/// with the given priority
void _monad_fiber_sleep(monad_fiber_wait_queue_t *wq, spinlock_t *wq_lock,
                        monad_fiber_prio_t wakeup_prio);

/// Wake up a fiber that was put to sleep on the given wait queue via an
/// earlier call to monad_fiber_sleep; to "wake up" here means "cause the
/// fiber to be rescheduled"
int _monad_fiber_wakeup(monad_fiber_t *fiber, monad_fiber_wait_queue_t *wq,
                        spinlock_t *wq_lock);

static inline bool monad_fiber_is_thread_fiber(const monad_fiber_t *fiber) {
    return fiber->ffunc == nullptr && fiber->thread_fiber_state != nullptr;
}

#if __cplusplus
} // extern "C"
#endif
