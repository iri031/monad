#pragma once

/**
 * @file
 *
 * This file defines the interface for our lightweight fiber library
 */

#include <stddef.h>
#include <stdint.h>

#include <monad/core/spinlock.h>
#include <monad/mem/cma/cma_alloc.h>

#if !defined(__clang__) && !defined(__has_feature)
    #define __has_feature(X) 0
#endif

#if __has_feature(address_sanitizer) || __SANITIZE_ADDRESS__
    #define MONAD_HAS_ASAN 1
#endif

#ifdef __cplusplus
extern "C"
{
#endif

/*
 * Forward declaration of opaque / incomplete types defined in other headers
 */

typedef void *monad_fcontext_t;
typedef struct monad_thread_executor monad_thread_executor_t;

/*
 * Types defined by fiber.h
 */

typedef struct monad_fiber monad_fiber_t;
typedef struct monad_fiber_attr monad_fiber_attr_t;
typedef struct monad_fiber_suspend_info monad_fiber_suspend_info_t;

typedef uintptr_t(monad_fiber_ffunc_t)(uintptr_t);
typedef int64_t monad_fiber_prio_t;

// TODO(ken): https://github.com/monad-crypto/monad-internal/issues/498
static monad_fiber_prio_t const MONAD_FIBER_PRIO_HIGHEST = INT64_MIN;
static monad_fiber_prio_t const MONAD_FIBER_PRIO_LOWEST = INT64_MAX - 1;
static monad_fiber_prio_t const MONAD_FIBER_PRIO_NO_CHANGE = INT64_MAX;

// TODO(ken): https://github.com/monad-crypto/monad-internal/issues/498
/// Various objects (fibers, wait channels, etc.) can be given a name for the
/// sake of debugging; the strlen(3) of the name cannot exceed this value
#define MONAD_FIBER_NAME_LEN (31)

enum monad_exec_state : unsigned;

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

/// Creation attributes for monad_fiber_create
struct monad_fiber_attr
{
    size_t stack_size;        ///< Size of fiber stack
    monad_allocator_t *alloc; ///< Allocator used for the monad_fiber_t object
};

/*
 * Public interface: functions that are called by users of the library
 */

/// Create a fiber, given a description of its attributes (if nullptr is passed,
/// the default attributes will be used)
int monad_fiber_create(
    monad_fiber_attr_t const *create_attr, monad_fiber_t **fiber);

/// Destroy a fiber previously created with monad_fiber_create
void monad_fiber_destroy(monad_fiber_t *fiber);

/// Set the function that the fiber will run; this may be called multiple times,
/// to reuse the fiber's resources (e.g., its stack) to run new functions
int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, uintptr_t fdata);

/// Returns the structure representing the currently executing fiber; returns
/// nullptr if the current execution context is not a fiber
monad_fiber_t *monad_fiber_self();

/// Begin running a fiber's function (or resume that function at the suspension
/// point, if it was suspended) on the given thread; this call returns the next
/// time the function suspends, and populates @ref suspend_info with info about
/// that suspension
int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info);

/// Similar to sched_yield(2) or pthread_yield_np(3), but for fibers: yields
/// from the currently-running fiber back to the previously-running fiber
void monad_fiber_yield(uintptr_t eval);

/// Get the name of a fiber, for debugging and instrumentation
int monad_fiber_get_name(monad_fiber_t *fiber, char *name, size_t size);

/// Set the name of a fiber, for debugging and instrumentation
int monad_fiber_set_name(monad_fiber_t *fiber, char const *name);

/// Returns true if the given fiber would execute immediately if monad_fiber_run
/// is called; be aware that this has a TOCTOU race in multithreaded code,
/// e.g., this could change asynchronously because of another thread
static bool monad_fiber_is_runnable(monad_fiber_t const *fiber);

struct monad_exec_stack
{
    void *stack_base;   ///< Lowest addr, incl. unusable memory (guard pages)
    void *stack_bottom; ///< Bottom of usable stack
    void *stack_top;    ///< Top of usable stack
};

struct monad_exec_stats
{
    size_t total_reset; ///< # of times monad_fiber_set_function is called
    size_t total_run;   ///< # of times fiber has been run (1 + <#resumed>)
    size_t total_sleep; ///< # of times exec slept on a sync. primitive
    size_t total_spurious_wakeups; ///< # times woken up just to sleep again
    size_t total_migrate;          ///< # of times moved between threads
};

enum monad_exec_context_type : unsigned
{
    MF_EXEC_NONE,
    MF_EXEC_HOST_THREAD,
    MF_EXEC_FIBER
};

/*
 * Fiber structures and inline functions
 */

/// An object representing an executable context; this represents the context
/// switching machinery used by both the fibers and the threads that run fibers
struct monad_exec_context
{
    enum monad_exec_context_type type;    ///< Ctx for fiber or regular thread?
    enum monad_exec_state state;          ///< Run state context is in
    monad_fcontext_t md_suspended_ctx;    ///< Suspended context pointer
    struct monad_exec_context *prev_exec; ///< Previously running exec context
    monad_thread_executor_t *thr_exec;    ///< For debug: last thread we ran on
    struct monad_exec_stack stack;        ///< Stack descriptor
    struct monad_exec_stats *stats;       ///< Statistics about this context
#if MONAD_HAS_ASAN
    void *fake_stack_save; ///< For ASAN fiber stack support
#endif
};

/// Object which represents a user-created fiber; users can set the priority
/// field of the current fiber(e.g., ` monad_fiber_self()->priority += 100` )
/// but should not directly write to other fields
struct monad_fiber
{
    struct monad_exec_context exec_ctx;  ///< Our context switching state
    alignas(64) monad_spinlock_t lock;   ///< Protects most fields
    monad_fiber_prio_t priority;         ///< Scheduling priority
    monad_fiber_ffunc_t *ffunc;          ///< Fiber function to run
    uintptr_t fdata;                     ///< Opaque user data passed to ffunc
    monad_fiber_attr_t create_attr;      ///< Attributes we were created with
    monad_memblk_t self_memblk;          ///< Dynamic memory block we live in
    struct monad_exec_stats stats;       ///< Statistics about this context
    char name[MONAD_FIBER_NAME_LEN + 1]; ///< Context name, for debugging
};

enum monad_exec_state : unsigned
{
    MF_STATE_INIT,      ///< Fiber function not run yet
    MF_STATE_CAN_RUN,   ///< Not running but able to run
    MF_STATE_RUNNING,   ///< Fiber or thread is running
    MF_STATE_EXEC_WAIT, ///< Suspended to execute another fiber
    MF_STATE_FINISHED   ///< Suspended by function return; fiber is finished
};

inline bool monad_fiber_is_runnable(monad_fiber_t const *fiber)
{
    MONAD_DEBUG_ASSERT(fiber != nullptr);
    return __atomic_load_n(&fiber->exec_ctx.state, __ATOMIC_SEQ_CST) ==
           MF_STATE_CAN_RUN;
}

#if __cplusplus
} // extern "C"
#endif
