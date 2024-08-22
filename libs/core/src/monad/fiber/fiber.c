/**
 * @file
 *
 * This file contains most of the implementation of the fiber library; see
 * fiber.md for the architectural documentation and implementation notes
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

// Used to communicate information about an in-progress switch between the
// monad_fiber_start_switch and _monad_fiber_finish_switch functions. These
// run on the same thread but different stacks (the former runs on the
// "switch_from" fiber's stack, the latter on the "switch_to" fiber's stack).
struct in_progress_fiber_switch
{
    monad_fiber_t *switch_from;
    monad_fiber_t *switch_to;
    enum monad_fiber_state switch_from_suspend_state;
    monad_fiber_suspend_info_t switch_from_suspend_info;
};

// Manually declare functions defined in fiber_thr.c
extern monad_fiber_t *_monad_get_thread_fiber();
extern void _monad_wakeup_thread_fiber(
    struct thread_fiber_state *tfs, monad_fiber_wait_queue_t *wq);

// When a fiber is first executed or is resumed after having been suspended,
// this function must be called to finish the switch.
//
// There are two places in the code where this can occur:
//
//   1. When a fiber initially begins running. This means at the beginning of
//      the fiber's entrypoint function (the function specified in the
//      monad_make_fcontext call)
//
//   2. Immediately after a call to monad_jump_fcontext returns, in the
//      monad_fiber_start_switch function. Note that a return from
//      monad_jump_fcontext implies we have been resumed from the suspension
//      implied by the jump, thus the switch we are finishing is not the same
//      one that was started by the start switch call
//
// This is an internal-only function but is declared "extern" so that it can be
// shared with fiber_thr.c
extern monad_fiber_suspend_info_t
_monad_fiber_finish_switch(struct monad_transfer_t xfer_from)
{
    pthread_t cur_thread;
    monad_fiber_t *cur_fiber;
    monad_fiber_t *prev_fiber;
    monad_fiber_suspend_info_t suspend_info;
    const struct in_progress_fiber_switch *const cur_switch =
        (struct in_progress_fiber_switch *)xfer_from.data;

#if MONAD_HAVE_ASAN
    // Finish the switch initiated by the most recent call to
    // _monad_fiber_begin_switch
    __sanitizer_finish_switch_fiber(
        cur_switch->switch_to->fake_stack_save, nullptr, nullptr);
#endif

    cur_fiber = tl_cur_fiber = cur_switch->switch_to;
    prev_fiber = cur_switch->switch_from;

    // Both fibers remain locked through the switch
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_fiber->lock));
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&prev_fiber->lock));

    // Remember where the switched-from fiber suspended, and update its state
    // from RUNNING to whatever suspension state it's entering
    prev_fiber->suspended_ctx = xfer_from.fctx;
    prev_fiber->state = cur_switch->switch_from_suspend_state;
    suspend_info = cur_switch->switch_from_suspend_info;

    if (MONAD_UNLIKELY(
            prev_fiber->state == MF_STATE_CAN_RUN &&
            prev_fiber->run_queue != nullptr)) {
        // This fiber can be run immediately despite being "suspended", so it
        // should be a yield; it also has a run queue we can just reschedule it
        // immediately; we don't need to unlock the fiber in that case, the
        // run queue expects it to be locked
        MONAD_DEBUG_ASSERT(suspend_info.suspend_type == MF_SUSPEND_YIELD);
        (void)monad_run_queue_try_push(prev_fiber->run_queue, prev_fiber);
    }
    else {
        monad_spinlock_unlock(&prev_fiber->lock);
    }

    // Finish book-keeping to become the current fiber; note that we cannot
    // access `cur_switch` below this point, as it lived on the previous
    // fiber's stack and now that the previous fiber is unlocked, it could
    // be destroyed at any time
    cur_thread = pthread_self();
    cur_fiber->state = MF_STATE_RUNNING;
    cur_fiber->prev_fiber = prev_fiber;
    if (MONAD_UNLIKELY(cur_fiber->last_thread != cur_thread)) {
        cur_fiber->last_thread = cur_thread;
        cur_fiber->last_thread_id = get_tl_tid();
        ++cur_fiber->stats.total_migrate;
    }
    ++cur_fiber->stats.total_run;

    monad_spinlock_unlock(&cur_fiber->lock);
    return suspend_info;
}

// Low-level machine-independent fiber switch function; this atomically suspends
// the current fiber and switches to the next fiber; the next fiber must
// immediately call _monad_fiber_finish_switch to complete this switch
static struct monad_transfer_t monad_fiber_start_switch(
    monad_fiber_t *cur_fiber, monad_fiber_t *next_fiber,
    enum monad_fiber_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
{
    // For ASAN:
    struct in_progress_fiber_switch cur_switch;
    [[maybe_unused]] size_t next_stack_size;
    [[maybe_unused]] void **fake_stack;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_fiber->lock));
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&next_fiber->lock));

    // XXX: assert switch is well-formed

    cur_switch.switch_from = cur_fiber;
    cur_switch.switch_to = next_fiber;
    cur_switch.switch_from_suspend_state = cur_suspend_state;
    cur_switch.switch_from_suspend_info.suspend_type = cur_suspend_type;
    cur_switch.switch_from_suspend_info.eval = eval;

#if MONAD_HAVE_ASAN
    // Tell ASAN we're going to switch to a new stack
    fake_stack = cur_suspend_state == MONAD_FIBER_FINISHED
                     ? nullptr
                     : &cur_fiber->fake_stack_save;
    next_stack_size =
        next_fiber->stack.stack_top - next_fiber->stack.stack_bottom;
    __sanitizer_start_switch_fiber(
        fake_stack, next_fiber->stack.stack_bottom, next_stack_size);
#endif

    // Call the machine-dependent fiber switch function, monad_jump_fcontext.
    // This atomically suspends our fiber and begins executing the next fiber
    // at its last suspension point. If we are resumed at some later time, it
    // will appear as through we've returned from this function call to
    // `monad_jump_fcontext`, and we will again be the current fiber.
    //
    // It returns a `struct monad_transfer_t`, with two members:
    //
    //   data - the `struct in_progress_fiber_switch *` for the switch that
    //          is returning control back to us
    //   fctx - the context pointer (effectively the suspension point) within
    //          the previously-running fiber, where it was suspended during the
    //          switch back to us
    return monad_jump_fcontext(next_fiber->suspended_ctx, &cur_switch);
}

extern void _monad_fiber_suspend(
    monad_fiber_t *cur_fiber, enum monad_fiber_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
{
    // Our suspension and scheduling model is that, upon suspension, we jump
    // back to the fiber that originally jumped to us. That fiber is typically
    // a lightweight scheduler, which decides which fiber to run next and
    // calls `monad_fiber_run`, thus we are usually jumping back into the body
    // of `monad_fiber_run`, which will return and report our suspension
    monad_fiber_t *const next_fiber = cur_fiber->prev_fiber;
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_fiber->lock));
    MONAD_SPINLOCK_LOCK(&next_fiber->lock);
    const struct monad_transfer_t xfer_from = monad_fiber_start_switch(
        cur_fiber, next_fiber, cur_suspend_state, cur_suspend_type, eval);
    asm volatile("" ::: "memory");
    (void)_monad_fiber_finish_switch(xfer_from);
}

[[noreturn]] static void fiber_entrypoint(struct monad_transfer_t xfer_from)
{
    // Entry point of a "user" fiber. When this function is called, we're
    // running on the fiber's stack for the first time (after the most recent
    // call to monad_fiber_set_function). We cannot directly return from this
    // function, but we can transfer control back to the fiber that jumped
    // here. In our model, that is the fiber that called the `monad_fiber_run`
    // function, which is typically a "thread fiber" running a lightweight
    // scheduler. The info needed to transfer control back to the suspension
    // point in `monad_fiber_run` is contained within the `xfer_from` argument
    uintptr_t rc;
    monad_fiber_t *self;

    // Finish the switch, then get our fiber
    (void)_monad_fiber_finish_switch(xfer_from);
    self = monad_fiber_self();

    // Enter the user fiber function
    rc = self->ffunc(self->fdata);

    // The fiber function returned, which appears as a kind of suspension to
    // the caller
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_fiber_suspend(self, MF_STATE_FINISHED, MF_SUSPEND_RETURN, rc);

    // This should be unreachable (monad_fiber_run should not resume us after
    // a "return" suspension)
    abort();
}

void monad_fiber_init(monad_fiber_t *fiber, monad_fiber_stack_t stack)
{
    memset(fiber, 0, sizeof *fiber);
    monad_spinlock_init(&fiber->lock);
    fiber->stack = stack;
}

int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, uintptr_t fdata)
{
    size_t stack_size;

    MONAD_SPINLOCK_LOCK(&fiber->lock);
    switch (fiber->state) {
    case MF_STATE_INIT:
        [[fallthrough]];
    case MF_STATE_CAN_RUN:
        [[fallthrough]];
    case MF_STATE_FINISHED:
        // It is legal to modify the fiber in these states
        break;

    default:
        // It is not legal to modify the fiber in these states
        monad_spinlock_unlock(&fiber->lock);
        return EBUSY;
    }
    stack_size = fiber->stack.stack_top - fiber->stack.stack_bottom;
    fiber->state = MF_STATE_CAN_RUN;
    fiber->priority = priority;
    fiber->suspended_ctx = monad_make_fcontext(
        fiber->stack.stack_top, stack_size, fiber_entrypoint);
    fiber->ffunc = ffunc;
    fiber->fdata = fdata;
    ++fiber->stats.total_reset;
    monad_spinlock_unlock(&fiber->lock);
    return 0;
}

monad_fiber_t *monad_fiber_self()
{
    return tl_cur_fiber != nullptr ? tl_cur_fiber : _monad_get_thread_fiber();
}

int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info)
{
    int err;
    struct monad_transfer_t resume_xfer;
    monad_fiber_suspend_info_t next_fiber_suspend_info;
    monad_fiber_t *const cur_fiber = monad_fiber_self();

    // The fiber is usually already locked, since fibers remain locked when
    // returned from the run queue. However, you can also run a fiber directly
    // e.g., in the test suite. Acquire the lock if we don't have it
    if (MONAD_UNLIKELY(!monad_spinlock_is_owned(&next_fiber->lock))) {
        MONAD_SPINLOCK_LOCK(&next_fiber->lock);
    }

    if (next_fiber->state != MF_STATE_CAN_RUN) {
        // The user tried to resume a fiber that is not in a run state that
        // can be resumed
        err = next_fiber->state == MF_STATE_FINISHED ? ENXIO : EBUSY;
        monad_spinlock_unlock(&next_fiber->lock);
        return err;
    }

    if (MONAD_UNLIKELY(!MONAD_SPINLOCK_TRY_LOCK(&cur_fiber->lock))) {
        monad_spinlock_unlock(&next_fiber->lock);
        return EDEADLOCK; // XXX: wrong return code?
    }

    // Switch into next_fiber
    resume_xfer = monad_fiber_start_switch(
        cur_fiber,
        next_fiber,
        MF_STATE_EXEC_WAIT,
        MF_SUSPEND_SLEEP,
        (uintptr_t)next_fiber);
    asm volatile("" ::: "memory");
    next_fiber_suspend_info = _monad_fiber_finish_switch(resume_xfer);
    if (suspend_info != nullptr) {
        memcpy(suspend_info, &next_fiber_suspend_info, sizeof *suspend_info);
    }
    return 0;
}

int monad_fiber_set_name(monad_fiber_t *fiber, char const *name)
{
    if (name == nullptr) {
        return EFAULT;
    }
    // XXX: not thread-safe, do we care enough to lock here? we also need a
    // get_name if we want to force them to use get/set functions
    (void)strncpy(fiber->name, name, MONAD_FIBER_NAME_LEN);
    return strlen(name) > MONAD_FIBER_NAME_LEN ? ENAMETOOLONG : 0;
}

void monad_fiber_yield(uintptr_t eval)
{
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_DEBUG_ASSERT(!monad_fiber_is_thread_fiber(self));
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_fiber_suspend(self, MF_STATE_CAN_RUN, MF_SUSPEND_YIELD, eval);
}

void _monad_fiber_sleep(
    monad_fiber_wait_queue_t *wq, monad_fiber_prio_t wakeup_prio)
{
    monad_fiber_t *const self = monad_fiber_self();
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(wq->lock));
    MONAD_SPINLOCK_LOCK(&self->lock);
    TAILQ_INSERT_TAIL(&wq->waiting_fibers, self, wait_link);
    self->wait_queue = wq;
    monad_spinlock_unlock(wq->lock);
    if (wakeup_prio != MONAD_FIBER_PRIO_NO_CHANGE) {
        self->priority = wakeup_prio;
    }
    ++self->stats.total_sleep;
    _monad_fiber_suspend(self, MF_STATE_WAIT_QUEUE, MF_SUSPEND_SLEEP, 0);
    MONAD_SPINLOCK_LOCK(wq->lock);
}

bool _monad_fiber_try_wakeup(monad_fiber_t *fiber, monad_fiber_wait_queue_t *wq)
{
    int rc;

    // Remove the fiber from the wait queue and mark it as runnable
    TAILQ_REMOVE(&wq->waiting_fibers, fiber, wait_link);
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    fiber->state = MF_STATE_CAN_RUN;
    monad_spinlock_unlock(wq->lock);
    fiber->prev_wq = fiber->wait_queue;
    fiber->wait_queue = nullptr;

    // Try to schedule the fiber to run again
    if (monad_fiber_is_thread_fiber(fiber)) {
        monad_spinlock_unlock(&fiber->lock);
        // Thread fiber "scheduling" always succeeds: it just signals the
        // sleeping thread's wakeup fiber
        _monad_wakeup_thread_fiber(fiber->thread_fs, wq);
        return true;
    }
    if (MONAD_UNLIKELY(fiber->run_queue == nullptr)) {
        // XXX: only for the test suite?
        monad_spinlock_unlock(&fiber->lock);
        return true;
    }
    if ((rc = monad_run_queue_try_push(fiber->run_queue, fiber)) == 0) {
        return true;
    }
    MONAD_ASSERT(rc != EBUSY);

    // Schedule failed because the run queue was too small; link us back
    // onto the wait queue
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    fiber->state = MF_STATE_WAIT_QUEUE;
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
