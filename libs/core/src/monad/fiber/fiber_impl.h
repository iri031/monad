#pragma once

#ifndef MONAD_FIBER_INTERNAL
    #error This is not a public interface, but a shared implementation file; do not include it
#endif

#include <sys/queue.h>
#include <threads.h>

#include <monad/fiber/fiber.h>

// Used to communicate information about an in-progress context switch between
// the start_context_switch and finish_context_switch functions. These run on
// the same host thread but different stacks (the former runs on the
// "switch_from" execution stack, the latter on the "switch_to" execution stack)
struct in_progress_context_switch
{
    struct monad_exec_context *switch_from;
    struct monad_exec_context *switch_to;
    enum monad_exec_state switch_from_suspend_state;
    monad_fiber_suspend_info_t switch_from_suspend_info;
};

/// Represents a thread (specifically the information about it needed to
/// execute a fiber)
struct monad_thread_executor
{
    struct monad_exec_context thread_ctx; ///< To save our ctx when suspended
    monad_fiber_t *cur_fiber;             ///< Fiber thread is running
    struct in_progress_context_switch
        cur_switch; ///< Describes current ctx switch happening on this thread
    thrd_t thread;  ///< Opaque system handle for the thread
    int thread_id;  ///< Public ID for the thread, for debugging
    SLIST_ENTRY(monad_thread_executor) next; ///< Linkage for all thread_locals
};

extern thread_local struct monad_thread_executor _tl_thr_exec;
extern void _monad_init_thread_executor(monad_thread_executor_t *thr_exec);

static inline monad_thread_executor_t *_monad_current_thread_executor()
{
    if (MONAD_UNLIKELY(_tl_thr_exec.thread_ctx.type == MF_EXEC_NONE)) {
        _monad_init_thread_executor(&_tl_thr_exec);
    }
    return &_tl_thr_exec;
}

static inline struct monad_exec_context *
_monad_current_exec_context(monad_thread_executor_t *thr_exec)
{
    return thr_exec->cur_fiber != nullptr ? &thr_exec->cur_fiber->exec_ctx
                                          : &thr_exec->thread_ctx;
}
