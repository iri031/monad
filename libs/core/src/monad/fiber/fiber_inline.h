/**
 * @file
 */

#ifndef MONAD_FIBER_INTERNAL
    #error This is not a public interface, but included into fiber.h for performance reasons; users should not include it
#endif

#include <errno.h>
#include <stdint.h>
#include <sys/queue.h>
#include <threads.h>

#include <monad/core/assert.h>
#include <monad/core/thread.h>

#include <monad-boost/context/fcontext.h>

#if MONAD_HAS_ASAN
    #include <sanitizer/asan_interface.h>
#endif

#ifdef __cplusplus
extern "C"
{
#endif

int _monad_run_queue_try_push_global(
    monad_run_queue_t *rq, monad_fiber_t *fiber);

static inline monad_fiber_t *
_monad_exec_context_to_fiber(struct monad_exec_context *exec_ctx)
{
    return exec_ctx->type == MF_EXEC_FIBER ? (monad_fiber_t *)exec_ctx
                                           : nullptr;
}

// This is only called from inside MONAD_DEBUG_ASSERT, thus why it is marked
// [[maybe_unused]]. It checks that a context is locked if it is a fiber; this
// prevents the run state from being altered during a switch
[[maybe_unused]] static inline bool
_monad_exec_context_is_safe(struct monad_exec_context *exec_ctx)
{
    monad_fiber_t *const fiber = _monad_exec_context_to_fiber(exec_ctx);
    return !fiber || monad_spinlock_is_owned(&fiber->lock);
}

#define RELEASE_EXEC_CONTEXT(CTX)                                              \
    do {                                                                       \
        monad_fiber_t *const fiber = _monad_exec_context_to_fiber(CTX);        \
        if (fiber != nullptr) {                                                \
            MONAD_SPINLOCK_UNLOCK(&fiber->lock);                               \
        }                                                                      \
    }                                                                          \
    while (0)

// Used to communicate information about an in-progress context switch between
// the start_context_switch and finish_context_switch functions. These run on
// the same host thread but different stacks (the former runs on the
// "switch_from" execution stack, the latter on the "switch_to" execution stack)
struct monad_in_progress_context_switch
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
    struct monad_exec_context thread_ctx; ///< Save thread's ctx when suspended
    monad_fiber_t *cur_fiber; ///< Fiber this thread is running (or nullptr)
    struct monad_in_progress_context_switch
        cur_switch; ///< Describes current ctx switch happening on this thread
    thrd_t thread; ///< Opaque system handle for the thread
    monad_tid_t thread_id; ///< Public ID for the thread, for debugging
    struct monad_exec_stats stats; ///< Statistics about this context
    SLIST_ENTRY(monad_thread_executor) next; ///< Linkage for all thread_locals
};

extern thread_local struct monad_thread_executor _monad_tl_thr_exec;

static inline monad_thread_executor_t *_monad_current_thread_executor()
{
    extern void _monad_init_thread_executor(monad_thread_executor_t * thr_exec);
    if (MONAD_UNLIKELY(_monad_tl_thr_exec.thread_ctx.type == MF_EXEC_NONE)) {
        _monad_init_thread_executor(&_monad_tl_thr_exec);
    }
    return &_monad_tl_thr_exec;
}

// When an execution stack is first used or is resumed after having been
// suspended, this function must be called to finish the context switch.
//
// There are two places in the code where this can occur:
//
//   1. When a fiber initially begins running. This means at the beginning of
//      the fiber's entrypoint function (the function specified in the
//      monad_make_fcontext call)
//
//   2. Immediately after a call to monad_jump_fcontext returns, in the
//      start_context_switch function. Note that a return from
//      monad_jump_fcontext implies we have been resumed from the suspension
//      implied by the jump, thus the switch we are finishing is not the same
//      one that was started by the start switch call
//
// Note even though this returns `monad_fiber_suspend_info_t`, the suspended
// context may not be a fiber: it could also be the thread context. The name of
// the return type is meant to be convenient for the API user.
static inline monad_fiber_suspend_info_t
_monad_finish_context_switch(struct monad_transfer_t xfer_from)
{
    struct monad_exec_context *cur_exec;
    struct monad_exec_context *prev_exec;
    monad_fiber_t *prev_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_thread_executor_t *const thr_exec =
        (monad_thread_executor_t *)xfer_from.data;
    struct monad_in_progress_context_switch const *const cur_switch =
        &thr_exec->cur_switch;

#if MONAD_HAS_ASAN
    // Finish the switch initiated by the most recent call to
    // _monad_fiber_begin_switch
    __sanitizer_finish_switch_fiber(
        cur_switch->switch_to->fake_stack_save, nullptr, nullptr);
#endif

    cur_exec = cur_switch->switch_to;
    prev_exec = cur_switch->switch_from;

    // Mark this execution context as the current fiber so that
    // `monad_fiber_self` will work; cur_fiber will be nullptr if this isn't a
    // fiber context
    thr_exec->cur_fiber = _monad_exec_context_to_fiber(cur_exec);

    MONAD_DEBUG_ASSERT(_monad_exec_context_is_safe(cur_exec));
    MONAD_DEBUG_ASSERT(_monad_exec_context_is_safe(prev_exec));

    // Remember where the switched-from context suspended, and update its state
    // from RUNNING to whatever suspension state it's entering
    prev_exec->md_suspended_ctx = xfer_from.fctx;
    prev_exec->state = cur_switch->switch_from_suspend_state;
    suspend_info = cur_switch->switch_from_suspend_info;

    if (MONAD_UNLIKELY(prev_exec->state == MF_STATE_CAN_RUN)) {
        // The previous context is ready to run again immediately despite the
        // fact that we just voluntarily switched away from it. This should
        // happen if it is a fiber that has just yielded. If the yielding fiber
        // also has a run queue, we can just reschedule it immediately. We
        // don't need (or want) to unlock the fiber in that case, because the
        // run queue expects it to be locked
        prev_fiber = _monad_exec_context_to_fiber(prev_exec);
        MONAD_DEBUG_ASSERT(
            prev_fiber != nullptr &&
            suspend_info.suspend_type == MF_SUSPEND_YIELD);
        if (MONAD_LIKELY(prev_fiber->run_queue != nullptr)) {
            (void)_monad_run_queue_try_push_global(
                prev_fiber->run_queue, prev_fiber);
        }
        else {
            MONAD_SPINLOCK_UNLOCK(&prev_fiber->lock);
        }
    }
    else {
        RELEASE_EXEC_CONTEXT(prev_exec);
    }

    // Finish book-keeping to become the new running context
    cur_exec->state = MF_STATE_RUNNING;
    cur_exec->prev_exec = prev_exec;
    if (MONAD_UNLIKELY(cur_exec->thr_exec != thr_exec)) {
        cur_exec->thr_exec = thr_exec;
        ++cur_exec->stats->total_migrate;
    }
    ++cur_exec->stats->total_run;

    RELEASE_EXEC_CONTEXT(cur_exec);
    return suspend_info;
}

// Low-level machine-independent context switch function; this atomically
// suspends the currently executing thread of control (either a thread proper
// or a fiber) and switches to the next one; the next execution context must
// immediately finish_context_switch to complete this switch
static inline struct monad_transfer_t _monad_start_context_switch(
    struct monad_exec_context *cur_exec, struct monad_exec_context *next_exec,
    enum monad_exec_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
{
    // For ASAN:
    [[maybe_unused]] size_t next_stack_size;
    [[maybe_unused]] void **fake_stack;
    monad_thread_executor_t *const thr_exec = cur_exec->thr_exec;
    struct monad_in_progress_context_switch *cur_switch = &thr_exec->cur_switch;

    MONAD_DEBUG_ASSERT(_monad_exec_context_is_safe(cur_exec));
    MONAD_DEBUG_ASSERT(_monad_exec_context_is_safe(next_exec));

    // XXX: assert switch is well-formed

    cur_switch->switch_from = cur_exec;
    cur_switch->switch_to = next_exec;
    cur_switch->switch_from_suspend_state = cur_suspend_state;
    cur_switch->switch_from_suspend_info.suspend_type = cur_suspend_type;
    cur_switch->switch_from_suspend_info.eval = eval;

#if MONAD_HAS_ASAN
    // Tell ASAN we're going to switch to a new stack. Even if the `switch_from`
    // fiber state is MF_STATE_FINISHED here, we don't pass nullptr to
    // mark that the stack is going away, since cur_switch still lives on this
    // stack and is read in _monad_fiber_finish_switch. This will trigger ASAN
    // if we tell it the stack is going away too early.
    // TODO(ken): this should be fixed, but all of this may be replaced by
    //   Niall's context machinery soon anyway
    fake_stack = &cur_exec->fake_stack_save;
    next_stack_size = (size_t)((uint8_t *)next_exec->stack.stack_top -
                               (uint8_t *)next_exec->stack.stack_bottom);
    __sanitizer_start_switch_fiber(
        fake_stack, next_exec->stack.stack_bottom, next_stack_size);
#endif

    // Call the machine-dependent context switch function, monad_jump_fcontext.
    // This atomically suspends this context and begins executing the next one
    // at its last suspension point. If we are resumed at some later time, it
    // will appear as through we've returned from this function call to
    // `monad_jump_fcontext`, and we will again be the currently running
    // context.
    //
    // It returns a `struct monad_transfer_t`, with two members:
    //
    //   data - the `struct monad_thread_executor_t *` for the switch that
    //          is returning control back to us
    //   fctx - the context pointer (effectively the suspension point) within
    //          the previously-running context, where it was suspended during
    //          the switch back to us
    return monad_jump_fcontext(next_exec->md_suspended_ctx, thr_exec);
}

static void _monad_suspend_fiber(
    monad_fiber_t *self, enum monad_exec_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
{
    // Our suspension and scheduling model is that, upon suspension, we jump
    // back to the context that originally jumped to us. That context is
    // typically running a lightweight scheduler, which decides which fiber to
    // run next and calls `monad_fiber_run`, thus we are usually jumping back
    // into the body of `monad_fiber_run`, which will return and report our
    // suspension
    monad_fiber_t *next_fiber;
    struct monad_exec_context *const next_exec = self->exec_ctx.prev_exec;
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&self->lock));
    next_fiber = _monad_exec_context_to_fiber(next_exec);
    if (MONAD_UNLIKELY(next_fiber != nullptr)) {
        MONAD_SPINLOCK_LOCK(&next_fiber->lock);
    }
    const struct monad_transfer_t xfer_from = _monad_start_context_switch(
        &self->exec_ctx, next_exec, cur_suspend_state, cur_suspend_type, eval);
    asm volatile("" ::: "memory");
    (void)_monad_finish_context_switch(xfer_from);
}

/*
 * Implementation of the public API
 */

inline monad_fiber_t *monad_fiber_self()
{
    monad_thread_executor_t *const thr_exec = _monad_current_thread_executor();
    return thr_exec->cur_fiber;
}

inline int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info)
{
    int err;
    struct monad_transfer_t resume_xfer;
    monad_fiber_t *cur_fiber;
    monad_fiber_suspend_info_t next_fiber_suspend_info;
    monad_thread_executor_t *thr_exec;
    struct monad_exec_context *cur_exec;
    struct monad_exec_context *next_exec;

    MONAD_DEBUG_ASSERT(next_fiber != nullptr);
    thr_exec = _monad_current_thread_executor();

    // Although most of the interface is written to allow fiber nesting (i.e.,
    // monad_fiber_run to be called from a fiber), this is neither used or
    // tested, so disallow it for now; we can add support later if needed
    MONAD_DEBUG_ASSERT(thr_exec->cur_fiber == nullptr);
    cur_exec = &thr_exec->thread_ctx;
    next_exec = &next_fiber->exec_ctx;

    // The fiber is usually already locked, since fibers remain locked when
    // returned from the run queue. However, you can also run a fiber directly
    // e.g., in the test suite. Acquire the lock if we don't have it
    if (MONAD_UNLIKELY(!monad_spinlock_is_owned(&next_fiber->lock))) {
        MONAD_SPINLOCK_LOCK(&next_fiber->lock);
    }

    if (next_exec->state != MF_STATE_CAN_RUN) {
        // The user tried to resume a fiber that is not in a run state that
        // can be resumed
        switch (next_exec->state) {
        case MF_STATE_INIT:
            [[fallthrough]];
        case MF_STATE_FINISHED:
            err = ENXIO;
            break;
        default:
            err = EBUSY;
            break;
        }
        MONAD_SPINLOCK_UNLOCK(&next_fiber->lock);
        return err;
    }

    cur_fiber = _monad_exec_context_to_fiber(cur_exec);
    if (cur_fiber != nullptr) {
        MONAD_SPINLOCK_LOCK(&cur_fiber->lock);
    }

    // Switch into next_fiber
    resume_xfer = _monad_start_context_switch(
        cur_exec,
        next_exec,
        MF_STATE_EXEC_WAIT,
        MF_SUSPEND_SLEEP,
        (uintptr_t)next_fiber);
    asm volatile("" ::: "memory");
    next_fiber_suspend_info = _monad_finish_context_switch(resume_xfer);
    if (suspend_info != nullptr) {
        memcpy(suspend_info, &next_fiber_suspend_info, sizeof *suspend_info);
    }
    return 0;
}

inline void monad_fiber_yield(uintptr_t eval)
{
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_DEBUG_ASSERT(self != nullptr);
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_suspend_fiber(self, MF_STATE_CAN_RUN, MF_SUSPEND_YIELD, eval);
}

#ifdef __cplusplus
} // extern "C"
#endif
