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
 * Forward declaration of opaque/incomplete types defined in other headers
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
/// sake of debugging; it cannot exceed this strlen(3) value
constexpr size_t MONAD_FIBER_NAME_LEN = 15;

enum monad_fiber_state : int;

enum monad_fiber_suspend_type : unsigned {
    MONAD_FIBER_SUSPEND_NONE,
    MONAD_FIBER_SUSPEND_YIELD,
    MONAD_FIBER_SUSPEND_SLEEP,
    MONAD_FIBER_SUSPEND_RETURN
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

/// Set the function that will run on a fiber; this may be called multiple
/// times, to reuse the fiber's resources (e.g., its stack) to run new functions
int monad_fiber_set_function(monad_fiber_t *fiber, monad_fiber_prio_t priority,
                             monad_fiber_ffunc_t *ffunc, uintptr_t fdata);

/// Returns the structure representing the currently executing fiber
monad_fiber_t *monad_fiber_self();

/// Begin running a new fiber (or resume that fiber at the suspension point, if
/// it's suspended); this function will return the next time the fiber suspends
int monad_fiber_run(monad_fiber_t *next_fiber,
                    monad_fiber_suspend_info_t *suspend_info);

/// Yield from the current fiber back to the previously executing fiber
void monad_fiber_yield(uintptr_t eval);

/// Set the name of a fiber, for debugging / instrumentation purposes
int monad_fiber_set_name(monad_fiber_t *fiber, const char *name);

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
    size_t total_run;     ///< # of times fiber has been run (1 + <resumed>)
    size_t total_sleep;   ///< # of times fiber slept on a sync. primitive
    size_t total_spurious_wakeups; ///< # times woken up just to sleep again
    size_t total_migrate; ///< # of times moved between threads
};

/*
 * Private interface: these functions are only called internally, by the
 * synchronization primitives (e.g., monad_fiber_channel_t,
 * monad_fiber_semaphore_t, etc.)
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
 * Fiber structures and inline functions - users may set the priority field
 * of the current fiber (e.g., `monad_fiber_self()->priority += 100`) but
 * should leave the other fields alone
 */

struct monad_fiber {
    monad_spinlock_t lock;                 ///< Protects most fiber fields
    enum monad_fiber_state state;          ///< Run state fiber is in
    monad_fiber_prio_t priority;           ///< Scheduling priority
    monad_fiber_wait_queue_t *wait_queue;  ///< Wait queue we're on
    TAILQ_ENTRY(monad_fiber) wait_link;    ///< Linkage for wait_queue
    TAILQ_ENTRY(monad_fiber) fibers_link;  ///< For crash dump "all fibers" list
    union {
        monad_run_queue_t *run_queue;         ///< Most recent run queue
        struct thread_fiber_state *thread_fs; ///< Book-keeping for thread fiber
    };
    monad_fcontext_t suspended_ctx;        ///< Stack pointer at susp. point
    monad_fiber_t *prev_fiber;             ///< Previously running fiber
    monad_fiber_suspend_info_t suspend_info; ///< Info about most recent susp.
    monad_fiber_wait_queue_t *prev_wq;     ///< For debug: remember last waitq
    pthread_t last_thread;                 ///< For debug: last thread we ran on
    int last_thread_id;                    ///< For debug: system ID of last thr
    struct monad_fiber_stats stats;        ///< Statistics about this fiber
    monad_fiber_ffunc_t *ffunc;            ///< Fiber function to run
    uintptr_t fdata;                       ///< Opaque user data passed to ffunc
    monad_fiber_stack_t stack;             ///< Descriptor for our stack
    char name[MONAD_FIBER_NAME_LEN + 1];   ///< Fiber name, for debugging
#if MONAD_HAVE_ASAN
    void *fake_stack_save;                 ///< For ASAN fiber support
#endif
};

enum monad_fiber_state : int {
    MONAD_FIBER_INIT,          ///< Fiber function not run yet
    MONAD_FIBER_CAN_RUN,       ///< Not running but able to run
    MONAD_FIBER_SLEEP,         ///< Asleep on a wait queue
    MONAD_FIBER_RUN_QUEUE,     ///< Scheduled on a run queue
    MONAD_FIBER_RUNNING,       ///< Fiber is running
    MONAD_FIBER_TW_SUSPEND,    ///< Thread wakeup fiber suspended (fiber_thr.c)
    MONAD_FIBER_RETURN         ///< Suspended by function return; finished
};

static inline bool monad_fiber_is_thread_fiber(const monad_fiber_t *fiber) {
    return fiber->ffunc == nullptr && fiber->thread_fs != nullptr;
}

#if __cplusplus
} // extern "C"
#endif
