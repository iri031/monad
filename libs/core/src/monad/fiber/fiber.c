/**
 * @file
 *
 * This file contains most of the implementation of the fiber library; see
 * fiber.md for a high-level description of how it works
 */

#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if MONAD_HAVE_ASAN
#include <sanitizer/asan_interface.h>
#endif

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/core/tl_tid.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_sync.h>
#include <monad/fiber/run_queue.h>

#include <monad-boost/context/fcontext.h>

static thread_local monad_fiber_t *tl_cur_fiber = nullptr;

// Manually declare functions from fiber_thr.c
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
//      monad_make_fcontext call)
//
//   2. Immediately after a call to monad_jump_fcontext returns, in the central
//      monad_fiber_start_switch function. Note that a return from
//      monad_jump_fcontext implies we have been resumed from the suspension
//      implied by the jump
//
// This is an internal-only function but is declared "extern" so that it can be
// shared with fiber_thr.c
extern monad_fiber_t*
_monad_fiber_finish_switch(monad_fiber_t *cur_fiber, monad_fiber_t *prev_fiber,
                           monad_fcontext_t prev_fiber_sctx) {
    pthread_t cur_thread;

#if MONAD_HAVE_ASAN
    // Finish the switch initiated by the most recent call to
    // _monad_fiber_begin_switch
    __sanitizer_finish_switch_fiber(cur_fiber->fake_stack_save, nullptr,
                                    nullptr);
#endif

    // Both fibers remain locked through the switch, and are released by the
    // landing site
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_fiber->lock));
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&prev_fiber->lock));

    // Remember where prev_fiber jumped from, and that it was the
    // previous fiber for cur_fiber; then unlock it
    prev_fiber->suspended_ctx = prev_fiber_sctx;
    cur_fiber->prev_fiber = prev_fiber;

    // Finish book-keeping to become the current fiber, then unlock it
    cur_thread = pthread_self();
    cur_fiber->state = MONAD_FIBER_RUNNING;
    if (cur_fiber->last_thread != cur_thread)
        ++cur_fiber->stats.total_migrate;
    cur_fiber->last_thread = cur_thread;
    cur_fiber->last_thread_id = get_tl_tid();
    ++cur_fiber->stats.total_run;

    return prev_fiber;
}

// Low-level fiber switch function; this atomically suspends the current fiber
// and switches to the next fiber; ; the next fiber
// must immediately call _monad_fiber_finish_switch to complete the switch
static monad_fiber_t *monad_fiber_start_switch(monad_fiber_t *cur_fiber,
                                               monad_fiber_t *next_fiber) {
    struct monad_transfer_t xfer_from;
    monad_fcontext_t next_fctx;
    [[maybe_unused]] size_t next_stack_size;
    [[maybe_unused]] void **fake_stack; // For ASAN

    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_fiber->lock));
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&next_fiber->lock));

    // XXX: assert switch is well-formed

    next_fctx = next_fiber->suspended_ctx;
    next_fiber->prev_fiber = cur_fiber;
    // Make the "current fiber" TLS variable point to the next fiber; it is not
    // safe to call monad_fiber_self() again until after the switch happens
    tl_cur_fiber = next_fiber;

#if MONAD_HAVE_ASAN
    // Tell ASAN we're going to switch to a new stack
    fake_stack = cur_fiber->state == MONAD_FIBER_RETURN
                     ? nullptr
                     : &cur_fiber->fake_stack_save;
    next_stack_size = next_fiber->stack.stack_top - next_fiber->stack.stack_bottom;
    __sanitizer_start_switch_fiber(fake_stack, next_fiber->stack.stack_bottom,
                                   next_stack_size);
#endif

    // Call the machine-dependent fiber switch function, monad_jump_fcontext.
    // This atomically suspends our fiber and begins executing the next fiber.
    // If we are resumed at some later time, it will appear as through we've
    // returned from the function call to `monad_jump_fcontext`, and we will
    // again be the current fiber.
    //
    // It returns a `monad_transfer_t` structure to us, with two members:
    //
    //   xfer_from.data - the `monad_fiber_t*` that returned control back to us
    //   xfer_from.fctx - the context pointer (effectively the suspension
    //                    point) within the previously-running fiber, where it
    //                    was suspended during the switch back to us
    xfer_from = monad_jump_fcontext(next_fctx, cur_fiber);

    // We are resumed, and are the current fiber again; complete the resume
    // half of the switch
    return _monad_fiber_finish_switch(cur_fiber, (monad_fiber_t*)xfer_from.data,
                                      xfer_from.fctx);
}

// External so it can be shared with fiber_thr.c
extern void _monad_fiber_suspend(monad_fiber_t *self,
                                 enum monad_fiber_state next_state,
                                 enum monad_fiber_suspend_type suspend_type,
                                 uintptr_t eval) {
    monad_fiber_t *prev_fiber;
    // Our suspension and scheduling model is that, upon suspension, we jump
    // back to the fiber that originally jumped to us. That fiber is typically
    // a lightweight scheduler, which decides which fiber to run next and
    // called `monad_fiber_run`
    monad_fiber_t *const next_fiber = self->prev_fiber;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&self->lock));
    self->state = next_state;
    self->suspend_info.suspend_type = suspend_type;
    self->suspend_info.eval = eval;
    MONAD_SPINLOCK_LOCK(&next_fiber->lock);

    // When the switch return, we are resumed and `prev_fiber` is the fiber
    // that resumed us; drop the locks and return
    prev_fiber = monad_fiber_start_switch(self, next_fiber);
    monad_spinlock_unlock(&prev_fiber->lock);
    monad_spinlock_unlock(&self->lock);
}

[[noreturn]] static void fiber_entrypoint(struct monad_transfer_t xfer_from) {
    // Entry point of a "user" fiber. When this function is called, we're
    // running on the fiber's stack for the first time (after the most recent
    // call to monad_make_fcontext). We do not directly return from this
    // function, but we can transfer control back to the context that jumped
    // here. In our model, that is a context that called the `monad_fiber_run`
    // function. The info needed to transfer control back to the suspension
    // point in `monad_fiber_run` is contained within the `xfer_from` argument
    uintptr_t rc;
    monad_fiber_t *const self = monad_fiber_self();
    monad_fiber_t *const prev_fiber =
        _monad_fiber_finish_switch(self, (monad_fiber_t*)xfer_from.data,
                                   xfer_from.fctx);
    monad_spinlock_unlock(&prev_fiber->lock);
    monad_spinlock_unlock(&self->lock);

    // Run the user fiber function
    rc = self->ffunc(self->fdata);

    // The fiber function returned, which appears as a kind of suspension
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_fiber_suspend(self, MONAD_FIBER_RETURN, MONAD_FIBER_SUSPEND_RETURN, rc);

    // This should be unreachable (monad_fiber_run should not resume us after
    // a "return" suspension)
    abort();
}

void monad_fiber_init(monad_fiber_t *fiber, monad_fiber_stack_t stack) {
    memset(fiber, 0, sizeof *fiber);
    monad_spinlock_init(&fiber->lock);
    fiber->stack = stack;
}

int monad_fiber_set_function(monad_fiber_t *fiber, monad_fiber_prio_t priority,
                             monad_fiber_ffunc_t *ffunc, uintptr_t fdata) {
    size_t stack_size;

    MONAD_SPINLOCK_LOCK(&fiber->lock);
    switch (fiber->state) {
    case MONAD_FIBER_INIT:
        [[fallthrough]];
    case MONAD_FIBER_CAN_RUN:
        [[fallthrough]];
    case MONAD_FIBER_RETURN:
        // It is legal to modify the fiber in these states
        break;

    default:
        monad_spinlock_unlock(&fiber->lock);
        return EBUSY;
    }
    stack_size = fiber->stack.stack_top - fiber->stack.stack_bottom;
    fiber->state = MONAD_FIBER_CAN_RUN;
    fiber->priority = priority;
    fiber->suspended_ctx =
        monad_make_fcontext(fiber->stack.stack_top, stack_size,
                            fiber_entrypoint);
    fiber->ffunc = ffunc;
    fiber->fdata = fdata;
    ++fiber->stats.total_reset;
    monad_spinlock_unlock(&fiber->lock);
    return 0;
}

monad_fiber_t *monad_fiber_self() {
    return tl_cur_fiber != nullptr ? tl_cur_fiber : _monad_get_thread_fiber();
}

int monad_fiber_run(monad_fiber_t *next_fiber,
                    monad_fiber_suspend_info_t *suspend_info) {
    int err;
    monad_fiber_t *prev_fiber;
    monad_fiber_t *const cur_fiber = monad_fiber_self();

    // The fiber is usually already locked, since fibers remain locked when
    // returned from the run queue. However you can also run a fiber directly,
    // e.g., in the test suite. Acquire the lock if we don't have it
    if (MONAD_UNLIKELY(!monad_spinlock_is_owned(&next_fiber->lock)))
        MONAD_SPINLOCK_LOCK(&next_fiber->lock);

    if (next_fiber->state != MONAD_FIBER_CAN_RUN) {
        // The user tried to resume a fiber that is not in a run state that
        // can be resumed
        err = next_fiber->state == MONAD_FIBER_RETURN ? EINVAL : EBUSY;
        monad_spinlock_unlock(&next_fiber->lock);
        return err;
    }

    if (MONAD_UNLIKELY(!MONAD_SPINLOCK_TRY_LOCK(&cur_fiber->lock))) {
        monad_spinlock_unlock(&next_fiber->lock);
        return EDEADLOCK; // XXX: wrong return code?
    }
    prev_fiber = monad_fiber_start_switch(cur_fiber, next_fiber);
    monad_spinlock_unlock(&cur_fiber->lock);

    if (suspend_info != nullptr)
        memcpy(suspend_info, &prev_fiber->suspend_info, sizeof *suspend_info);
    if (prev_fiber->suspend_info.suspend_type == MONAD_FIBER_SUSPEND_YIELD &&
        prev_fiber->run_queue != nullptr)
        return monad_run_queue_try_push(prev_fiber->run_queue, prev_fiber);
    monad_spinlock_unlock(&prev_fiber->lock);

    return 0;
}

int monad_fiber_set_name(monad_fiber_t *fiber, const char *name) {
    if (name == nullptr)
        return EFAULT;
    // XXX: not thread, who cares?
    (void)strncpy(fiber->name, name, MONAD_FIBER_NAME_LEN);
    return strlen(name) > MONAD_FIBER_NAME_LEN ? ENAMETOOLONG : 0;
}

void monad_fiber_yield(uintptr_t eval) {
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_DEBUG_ASSERT(!monad_fiber_is_thread_fiber(self));
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_fiber_suspend(self, MONAD_FIBER_CAN_RUN, MONAD_FIBER_SUSPEND_YIELD,
                         eval);
}

void _monad_fiber_sleep(monad_fiber_wait_queue_t *wq,
                        monad_fiber_prio_t wakeup_prio) {
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_SPINLOCK_LOCK(&self->lock);
    TAILQ_INSERT_TAIL(&wq->waiting_fibers, self, wait_link);
    self->wait_queue = wq;
    monad_spinlock_unlock(wq->lock);
    if (wakeup_prio != MONAD_FIBER_PRIO_NO_CHANGE)
        self->priority = wakeup_prio;
    ++self->stats.total_sleep;
    _monad_fiber_suspend(self, MONAD_FIBER_SLEEP, MONAD_FIBER_SUSPEND_SLEEP, 0);
    MONAD_SPINLOCK_LOCK(wq->lock);
}

bool _monad_fiber_try_wakeup(monad_fiber_t *fiber,
                             monad_fiber_wait_queue_t *wq)
{
    int rc;

    // Remove the fiber from the wait queue
    TAILQ_REMOVE(&wq->waiting_fibers, fiber, wait_link);
    monad_spinlock_unlock(wq->lock);
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    fiber->state = MONAD_FIBER_CAN_RUN;
    fiber->prev_wq = fiber->wait_queue;
    fiber->wait_queue = nullptr;

    // Try to schedule the fiber to run again
    if (monad_fiber_is_thread_fiber(fiber)) {
        monad_spinlock_unlock(&fiber->lock);
        // Thread fiber scheduling always succeeds
        _monad_wakeup_thread_fiber(fiber->thread_fs, wq);
        return true;
    }
    if ((rc = monad_run_queue_try_push(fiber->run_queue, fiber)) == 0)
        return true;
    MONAD_ASSERT(rc != EBUSY);

    // Schedule failed because the run queue was too small; link us back
    // onto the wait queue
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    fiber->state = MONAD_FIBER_SLEEP;
    fiber->wait_queue = fiber->prev_wq;
    fiber->prev_wq = nullptr;
    ++fiber->stats.total_sleep;
    ++fiber->stats.total_spurious_wakeups;
    monad_spinlock_unlock(&fiber->lock);

    MONAD_SPINLOCK_LOCK(wq->lock);
    TAILQ_INSERT_HEAD(&wq->waiting_fibers, fiber, wait_link);
    monad_spinlock_unlock(wq->lock);
    return false;
}