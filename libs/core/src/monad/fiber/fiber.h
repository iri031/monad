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

/*
 * Forward declaration of opaque / incomplete types defined in other headers
 */

typedef void *monad_fcontext_t;
struct thread_fiber_state;
typedef struct monad_run_queue monad_run_queue_t;
typedef struct monad_fiber_wait_queue monad_fiber_wait_queue_t;

/*
 * Types defined by fiber.h
 */

typedef struct monad_fiber monad_fiber_t;
typedef struct monad_fiber_stack monad_fiber_stack_t;
typedef struct monad_fiber_suspend_info monad_fiber_suspend_info_t;

typedef uintptr_t (monad_fiber_ffunc_t)(uintptr_t);
typedef int64_t monad_fiber_prio_t;

constexpr monad_fiber_prio_t MONAD_FIBER_PRIO_HIGHEST = INT64_MIN;
constexpr monad_fiber_prio_t MONAD_FIBER_PRIO_LOWEST = INT64_MAX - 1;
constexpr monad_fiber_prio_t MONAD_FIBER_PRIO_NO_CHANGE = INT64_MAX;

/// Various objects (fibers, wait channels, etc.) can be given a name for the
/// sake of debugging; the strlen(3) of the name cannot exceed this value
constexpr size_t MONAD_FIBER_NAME_LEN = 31;

enum monad_fiber_state : unsigned;

enum monad_fiber_suspend_type : unsigned {
    MF_SUSPEND_NONE,
    MF_SUSPEND_YIELD,
    MF_SUSPEND_SLEEP,
    MF_SUSPEND_RETURN
};

struct monad_fiber_suspend_info {
    enum monad_fiber_suspend_type suspend_type;  ///< Reason for last suspension
    uintptr_t eval;                              ///< Value (for YIELD / RETURN)
};

/*
 * Public interface: functions that are called by users of the library
 */

/// Initialize a fiber, given a description of its stack area
void monad_fiber_init(monad_fiber_t *fiber, monad_fiber_stack_t stack);

/// Set the function that the fiber will run; this may be called multiple times,
/// to reuse the fiber's resources (e.g., its stack) to run new functions
int monad_fiber_set_function(monad_fiber_t *fiber, monad_fiber_prio_t priority,
                             monad_fiber_ffunc_t *ffunc, uintptr_t fdata);

/// Returns the structure representing the currently executing fiber
monad_fiber_t *monad_fiber_self();

/// Begin running a fiber's function, or resume that function at the suspension
/// point, if it was suspended; this call returns the next time the function
/// suspends, and populates @ref suspend_info with info about that suspension
int monad_fiber_run(monad_fiber_t *next_fiber,
                    monad_fiber_suspend_info_t *suspend_info);

/// Similar to sched_yield(2) or pthread_yield_np(3), but for fibers: yields
/// from the currently-running fiber back to the previously-running fiber
void monad_fiber_yield(uintptr_t eval);

/// Set the name of a fiber, for debugging and instrumentation
int monad_fiber_set_name(monad_fiber_t *fiber, const char *name);

/// Determine if the given fiber is a thread fiber; see fiber.md for an
/// explanation of thread fibers
static inline bool monad_fiber_is_thread_fiber(const monad_fiber_t *fiber);

struct monad_fiber_stack {
    void *stack_base;    ///< Lowest addr, incl. unusable memory (guard pages)
    void *stack_bottom;  ///< Bottom of usable stack
    void *stack_top;     ///< Top of usable stack
};

struct monad_fiber_stats {
    size_t total_reset;   ///< # of times monad_fiber_set_function is called
    size_t total_run;     ///< # of times fiber has been run (1 + <#resumed>)
    size_t total_sleep;   ///< # of times fiber slept on a sync. primitive
    size_t total_spurious_wakeups; ///< # times woken up just to sleep again
    size_t total_migrate; ///< # of times moved between threads
};

/*
 * Private interface: these functions are only called by other parts of the
 * fiber library, e.g. by synchronization primitives like monad_fiber_channel_t
 */

/// Put the current fiber to sleep on the given wait queue, to be woken up
/// with the given priority
void _monad_fiber_sleep(monad_fiber_wait_queue_t *wq,
                        monad_fiber_prio_t wakeup_prio);

/// Wake up a fiber that was put to sleep on the given wait queue via an
/// earlier call to _monad_fiber_sleep; to "wake up" means "cause the fiber
/// to be rescheduled"; this can fail, e.g., if the scheduler queue is full
bool _monad_fiber_try_wakeup(monad_fiber_t *fiber,
                             monad_fiber_wait_queue_t *wq);

/*
 * Fiber structures and inline functions - users can set the priority field
 * of the current fiber (e.g., `monad_fiber_self()->priority += 100`) but
 * should not directly write to other fields
 */

struct monad_fiber {
    alignas(64) monad_spinlock_t lock;     ///< Protects most fiber fields
    enum monad_fiber_state state;          ///< Run state fiber is in
    monad_fiber_prio_t priority;           ///< Scheduling priority
    monad_fiber_wait_queue_t *wait_queue;  ///< Wait queue we're on
    TAILQ_ENTRY(monad_fiber) wait_link;    ///< Linkage for wait_queue
    union {
        monad_run_queue_t *run_queue;         ///< Most recent run queue
        struct thread_fiber_state *thread_fs; ///< Book-keeping for thread fiber
    };
    monad_fcontext_t suspended_ctx;        ///< Stack pointer at susp. point
    monad_fiber_t *prev_fiber;             ///< Previously running fiber
    monad_fiber_wait_queue_t *prev_wq;     ///< For debug: remember last waitq
    pthread_t last_thread;                 ///< For debug: last thread we ran on
    int last_thread_id;                    ///< For debug: system ID of last thr
    struct monad_fiber_stats stats;        ///< Statistics about this fiber
    monad_fiber_ffunc_t *ffunc;            ///< Fiber function to run
    uintptr_t fdata;                       ///< Opaque user data passed to ffunc
    monad_fiber_stack_t stack;             ///< Descriptor for fiber's stack
    TAILQ_ENTRY(monad_fiber) fibers_link;  ///< For crash dump "all fibers" list
    char name[MONAD_FIBER_NAME_LEN + 1];   ///< Fiber name, for debugging
#if MONAD_HAVE_ASAN
    void *fake_stack_save;                 ///< For ASAN fiber stack support
#endif
};

enum monad_fiber_state : unsigned {
    MF_STATE_INIT,          ///< Fiber function not run yet
    MF_STATE_CAN_RUN,       ///< Not running but able to run
    MF_STATE_WAIT_QUEUE,    ///< Asleep on a wait queue
    MF_STATE_RUN_QUEUE,     ///< Scheduled on a run queue
    MF_STATE_RUNNING,       ///< Fiber is running
    MF_STATE_EXEC_WAIT,     ///< Suspended to execute another fiber
    MF_STATE_FINISHED       ///< Suspended by function return; finished
};

static inline bool monad_fiber_is_thread_fiber(const monad_fiber_t *fiber) {
    return fiber->ffunc == nullptr && fiber->thread_fs != nullptr;
}

#if __cplusplus
} // extern "C"
#endif
