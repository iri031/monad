#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if MONAD_HAVE_ASAN
#include <sanitizer/asan_interface.h>
#endif

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/tl_tid.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/run_queue.h>

#include "fiber_ctx.h"

static thread_local monad_fiber_t *volatile tl_cur_fiber = nullptr;

struct thread_fiber_state;
extern monad_fiber_t *_monad_get_thread_fiber();
extern void _monad_wakeup_thread_fiber(struct thread_fiber_state *tfs,
                                       monad_fiber_wait_queue_t *wq);

// When a fiber is first executed or is resumed after having been suspended,
// this function must be called to update that fiber's internal data.
//
// There are two places in the code where this can occur:
//
//   1. When a fiber initially begins running. This means at the beginning of
//      the fiber's entrypoint function (the function specified in the
//      make_fcontext call)
//
//   2. Immediately after a call to jump_fcontext returns, in the central
//      _monad_fiber_start_switch function. Note that a return from
//      jump_fcontext implies we have been resumed from the suspension implied
//      by the jump
extern monad_fiber_t*
_monad_fiber_finish_switch(monad_fiber_t *cur_fiber,
                           monad_fiber_transfer_t xfer_from)
{
    const pthread_t cur_thread = pthread_self();

#if MONAD_HAVE_ASAN
    // Finish the switch initiated by the most recent call to
    // _monad_fiber_begin_switch
    __sanitizer_finish_switch_fiber(cur_fiber->fake_stack_save, nullptr,
                                    nullptr);
#endif

    // Remember where we jumped from
    cur_fiber->prev_fiber = xfer_from.prev_fiber;
    cur_fiber->prev_fiber->fctx = xfer_from.prev_fctx;

    // Book-keeping to become the current fiber
    cur_fiber->status.state = MONAD_FIBER_RUN;
    if (cur_fiber->last_thread != cur_thread)
        ++cur_fiber->stats.total_migrate;
    cur_fiber->last_thread = cur_thread;
    cur_fiber->last_thread_id = get_tl_tid();
    ++cur_fiber->stats.total_run;

    return cur_fiber;
}

// Low-level fiber switch function; this atomically suspends the current fiber
// and switches to the next fiber; it is an internal-only function but is
// declared "extern" so that it can be shared with fiber_thr.c; the next fiber
// must immediately call _monad_fiber_finish_switch to complete the switch
extern void _monad_fiber_start_switch(monad_fiber_t *cur_fiber,
                                      monad_fiber_t *next_fiber) {
    monad_fiber_transfer_t xfer_from;
    [[maybe_unused]] size_t next_stack_size;
    [[maybe_unused]] void **fake_stack; // For ASAN

    next_fiber->prev_fiber = cur_fiber;
    // Make the "current fiber" TLS variable point to the next fiber; it is not
    // safe to call monad_fiber_self() again until after the switch happens
    tl_cur_fiber = next_fiber;

#if MONAD_HAVE_ASAN
    // Tell ASAN we're going to switch to a new stack
    fake_stack = cur_fiber->status.state == MONAD_FIBER_RETURN
                     ? nullptr
                     : &cur_fiber->fake_stack_save;
    next_stack_size = next_fiber->stack.stack_top - next_fiber->stack.stack_bottom;
    __sanitizer_start_switch_fiber(fake_stack, next_fiber->stack.stack_bottom,
                                   next_stack_size);
#endif

    // Call the machine-dependent fiber switch function, jump_fcontext. This
    // atomically suspends our fiber and begins executing the next fiber. If we
    // are resumed at some later time, it will appear as through we've returned
    // from the function call to `jump_fcontext`, and we will again be the
    // current fiber.
    //
    // It returns a `monad_fiber_transfer_t` structure to us, with two members:
    //
    //   xfer_from.prev_fiber - the `monad_fiber_t*` that returned control back
    //                          to us
    //   xfer_from.prev_fctx  - the context pointer (effectively the suspension
    //                          point) within `xfer_from.prev_fiber` where it
    //                          was suspended during the switch back to us
    xfer_from = jump_fcontext(next_fiber->fctx, cur_fiber);

    // We are resumed, and are the current fiber again; complete the resume
    // half of the switch. Note that it is *NOT* safe to access any local
    // variables that were set earlier in this function (namely, cur_fiber)
    // since we may be running on a different thread now, and any callee-saved
    // values in this stack frame are potentially wrong. The current fiber can
    // be accessed via monad_fiber_self(), which was setup by the prologue to
    // our arrival here
    (void)_monad_fiber_finish_switch(monad_fiber_self(), xfer_from);
}

static void suspend_fiber(monad_fiber_t *fiber, enum monad_fiber_state state,
                          uintptr_t eval) {
    fiber->status.state = state;
    fiber->status.eval = eval;

    // Our suspension and scheduling model is that, upon suspension, we jump
    // back to the fiber that originally jumped to us. That fiber is typically
    // a lightweight scheduler, which decides which fiber to run next
    _monad_fiber_start_switch(fiber, fiber->prev_fiber);
}

[[noreturn]] static void fiber_entrypoint(monad_fiber_transfer_t xfer_from) {
    // Entry point of a "user" fiber. When this function is called, we're
    // running on the fiber's stack for the first time (after the most recent
    // call to make_fcontext). We do not directly return from this function, but
    // we can transfer control back to the context that jumped here. In our
    // model, that is usually the context called `monad_fiber_run`. The thread
    // context needed to transfer control back to there is contained within the
    // `xfer_from` argument
    uintptr_t rc;
    monad_fiber_t *const fiber =
        _monad_fiber_finish_switch(monad_fiber_self(), xfer_from);

    // Run the user fiber function
    rc = fiber->ffunc(fiber->fdata);

    // The fiber function returned, which appears as a kind of suspension
    suspend_fiber(fiber, MONAD_FIBER_RETURN, rc);

    // This should be unreachable (monad_fiber_run should not resume us after
    // a "return" suspension)
    abort();
}

void monad_fiber_init(monad_fiber_t *fiber, monad_fiber_stack_t stack) {
    memset(fiber, 0, sizeof *fiber);
    fiber->stack = stack;
}

monad_fiber_t*
monad_fiber_set_function(monad_fiber_t *fiber, monad_fiber_prio_t priority,
                         monad_fiber_ffunc_t *ffunc, uintptr_t fdata) {
    const size_t stack_size = fiber->stack.stack_top - fiber->stack.stack_bottom;
    fiber->priority = priority;
    fiber->ffunc = ffunc;
    fiber->fdata = fdata;
    fiber->fctx = make_fcontext(fiber->stack.stack_top, stack_size,
                                fiber_entrypoint);
    fiber->status.state = MONAD_FIBER_INIT;
    ++fiber->stats.total_reset;
    return fiber;
}

monad_fiber_t *monad_fiber_self() {
    return tl_cur_fiber != nullptr ? tl_cur_fiber : _monad_get_thread_fiber();
}

monad_fiber_status_t monad_fiber_run(monad_fiber_t *fiber) {
    if (MONAD_UNLIKELY(fiber->status.state == MONAD_FIBER_RETURN)) {
        // The user tried to resume a fiber that returned; this is fatal
        fprintf(stderr, "FATAL: fiber %p:%zu tried to resume after the return "
                        "suspension point (returned %lu)", fiber->ffunc,
                fiber->fdata, fiber->status.eval);
        abort();
    }
    _monad_fiber_start_switch(monad_fiber_self(), fiber);
    return fiber->status;
}

void monad_fiber_yield(uintptr_t eval) {
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_ASSERT(!monad_fiber_is_thread_fiber(self)); // These can't yield
    suspend_fiber(self, MONAD_FIBER_YIELD, eval);
}

void _monad_fiber_sleep(monad_fiber_wait_queue_t *wq, spinlock_t *wq_lock,
                        monad_fiber_prio_t wakeup_prio) {
    monad_fiber_t *const self = monad_fiber_self();
    TAILQ_INSERT_TAIL(wq, self, wait_link);
    spinlock_unlock(wq_lock);
    self->wait_queue = wq;
    if (wakeup_prio != MONAD_FIBER_PRIO_NO_CHANGE)
        self->priority = wakeup_prio;
    ++self->stats.total_sleep;
    suspend_fiber(self, MONAD_FIBER_SLEEP, 0);
    self->wait_queue = nullptr;
    spinlock_lock(wq_lock);
}

int _monad_fiber_wakeup(monad_fiber_t *fiber, monad_fiber_wait_queue_t *wq,
                        spinlock_t *wq_lock) {
    // Remove the fiber from the wait queue. We don't clear `fiber->wait_queue`
    // here, we let the resume side clear it
    TAILQ_REMOVE(wq, fiber, wait_link);
    spinlock_unlock(wq_lock);

    // Schedule the fiber to run again
    if (monad_fiber_is_thread_fiber(fiber)) {
        _monad_wakeup_thread_fiber(fiber->thread_fiber_state, wq);
        return 0;
    }
    else
        return monad_run_queue_try_push(fiber->run_queue, fiber);
}