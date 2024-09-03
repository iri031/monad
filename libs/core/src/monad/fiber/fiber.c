/**
 * @file
 *
 * This file contains most of the implementation of the fiber library; see
 * fiber-impl.md for the implementation notes
 */

#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <sys/mman.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>

#include <monad-boost/context/fcontext.h>

#if MONAD_HAS_ASAN
    #include <sanitizer/asan_interface.h>
#endif

#define MONAD_FIBER_INTERNAL
#include "fiber_impl.h"

static monad_fiber_attr_t g_default_fiber_attr = {
    .stack_size = 1 << 17, // 128 KiB
    .alloc = nullptr       // Default allocator
};

static int alloc_fiber_stack(struct monad_exec_stack *stack, size_t *stack_size)
{
    int const stack_protection = PROT_READ | PROT_WRITE;
    int const stack_flags = MAP_ANONYMOUS | MAP_PRIVATE | MAP_STACK;

    int const page_size = getpagesize();
    if (stack_size == nullptr || stack == nullptr) {
        return EFAULT;
    }
    if ((ptrdiff_t)*stack_size - page_size < page_size) {
        return EINVAL;
    }
    stack->stack_base =
        mmap(nullptr, *stack_size, stack_protection, stack_flags, -1, 0);
    if (stack->stack_base == MAP_FAILED) {
        return errno;
    }
    if (mprotect(stack->stack_base, page_size, PROT_NONE) == -1) {
        return errno;
    }
    *stack_size -= page_size;
    stack->stack_bottom = (uint8_t *)stack->stack_base + page_size;
    stack->stack_top = (uint8_t *)stack->stack_bottom + *stack_size;
    return 0;
}

static void dealloc_fiber_stack(struct monad_exec_stack stack)
{
    size_t const mapped_size = (size_t)((uint8_t const *)stack.stack_top -
                                        (uint8_t const *)stack.stack_base);
    munmap(stack.stack_base, mapped_size);
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
static monad_fiber_suspend_info_t
finish_context_switch(struct monad_transfer_t xfer_from)
{
    struct monad_exec_context *cur_exec;
    struct monad_exec_context *prev_exec;
    monad_fiber_suspend_info_t suspend_info;
    monad_thread_executor_t *const thr_exec = xfer_from.data;
    struct in_progress_context_switch const *const cur_switch =
        &thr_exec->cur_switch;

#if MONAD_HAS_ASAN
    // Finish the switch initiated by the most recent call to
    // _monad_fiber_begin_switch
    __sanitizer_finish_switch_fiber(
        cur_switch->switch_to->fake_stack_save, nullptr, nullptr);
#endif

    cur_exec = cur_switch->switch_to;
    prev_exec = cur_switch->switch_from;

    // If the context we're switching is a fiber, mark it as the current one
    // for this thread so that `monad_fiber_self()` will work.
    thr_exec->cur_fiber =
        cur_exec->type == MF_EXEC_FIBER ? (monad_fiber_t *)cur_exec : nullptr;

    // Both context objects remain locked through the switch
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_exec->lock));
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&prev_exec->lock));

    // Remember where the switched-from context suspended, and update its state
    // from RUNNING to whatever suspension state it's entering
    prev_exec->md_suspended_ctx = xfer_from.fctx;
    prev_exec->state = cur_switch->switch_from_suspend_state;
    suspend_info = cur_switch->switch_from_suspend_info;
    MONAD_SPINLOCK_UNLOCK(&prev_exec->lock);

    // Finish book-keeping to become the new running context
    cur_exec->state = MF_STATE_RUNNING;
    cur_exec->prev_exec = prev_exec;
    if (MONAD_UNLIKELY(cur_exec->thr_exec != thr_exec)) {
        cur_exec->thr_exec = thr_exec;
        ++cur_exec->stats.total_migrate;
    }
    ++cur_exec->stats.total_run;

    MONAD_SPINLOCK_UNLOCK(&cur_exec->lock);
    return suspend_info;
}

// Low-level machine-independent context switch function; this atomically
// suspends the currently executing thread of control (either a thread proper
// or a fiber) and switches to the next one; the next execution context must
// immediately finish_context_switch to complete this switch
static struct monad_transfer_t start_context_switch(
    struct monad_exec_context *cur_exec, struct monad_exec_context *next_exec,
    enum monad_exec_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
{
    // For ASAN:
    [[maybe_unused]] size_t next_stack_size;
    [[maybe_unused]] void **fake_stack;
    monad_thread_executor_t *const thr_exec = cur_exec->thr_exec;
    struct in_progress_context_switch *cur_switch = &thr_exec->cur_switch;

    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&cur_exec->lock));
    MONAD_DEBUG_ASSERT(monad_spinlock_is_owned(&next_exec->lock));

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
    next_stack_size =
        next_exec->stack.stack_top - next_exec->stack.stack_bottom;
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

static void suspend_fiber(
    struct monad_exec_context *cur_exec,
    enum monad_exec_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
{
    // Our suspension and scheduling model is that, upon suspension, we jump
    // back to the context that originally jumped to us. That context is
    // typically running a lightweight scheduler, which decides which fiber to
    // run next and calls `monad_fiber_run`, thus we are usually jumping back
    // into the body of `monad_fiber_run`, which will return and report our
    // suspension
    struct monad_exec_context *const next_exec = cur_exec->prev_exec;
    MONAD_DEBUG_ASSERT(
        monad_spinlock_is_owned(&cur_exec->lock) &&
        cur_exec->type == MF_EXEC_FIBER);
    MONAD_SPINLOCK_LOCK(&next_exec->lock);
    const struct monad_transfer_t xfer_from = start_context_switch(
        cur_exec, next_exec, cur_suspend_state, cur_suspend_type, eval);
    asm volatile("" ::: "memory");
    (void)finish_context_switch(xfer_from);
}

[[noreturn]] static void fiber_entrypoint(struct monad_transfer_t xfer_from)
{
    // Entry point of a "user" fiber. When this function is called, we're
    // running on the fiber's stack for the first time (after the most recent
    // call to monad_fiber_set_function). We cannot directly return from this
    // function, but we can transfer control back to the execution context that
    // jumped here. In our model, that is the context that called the
    // `monad_fiber_run` function, which is typically a regular thread running
    // a lightweight scheduler. The info needed to transfer control back to the
    // suspension point in `monad_fiber_run` is contained within the `xfer_from`
    // argument
    uintptr_t rc;
    monad_fiber_t *self;

    // Finish the switch, then get our fiber
    (void)finish_context_switch(xfer_from);
    self = monad_fiber_self();

    // Call the user fiber function
    rc = self->ffunc(self->fdata);

    // The fiber function returned, which appears as a kind of suspension to
    // the caller
    MONAD_SPINLOCK_LOCK(&self->exec_ctx.lock);
    suspend_fiber(&self->exec_ctx, MF_STATE_FINISHED, MF_SUSPEND_RETURN, rc);

    // This should be unreachable (monad_fiber_run should not resume us after
    // a "return" suspension)
    abort();
}

int monad_fiber_create(monad_fiber_attr_t const *attr, monad_fiber_t **fiber)
{
    monad_memblk_t memblk;
    struct monad_exec_stack fiber_stack;
    monad_fiber_t *f;
    size_t stack_size;
    int rc;

    if (fiber == nullptr) {
        return EFAULT;
    }
    *fiber = nullptr;
    if (attr == nullptr) {
        attr = &g_default_fiber_attr;
    }
    stack_size = attr->stack_size;
    rc = alloc_fiber_stack(&fiber_stack, &stack_size);
    if (rc != 0) {
        return rc;
    }
    rc =
        monad_cma_alloc(attr->alloc, sizeof **fiber, alignof * *fiber, &memblk);
    if (rc != 0) {
        dealloc_fiber_stack(fiber_stack);
        return rc;
    }
    *fiber = f = memblk.ptr;
    memset(f, 0, sizeof *f);
    monad_spinlock_init(&f->exec_ctx.lock);
    f->exec_ctx.type = MF_EXEC_FIBER;
    f->exec_ctx.state = MF_STATE_INIT;
    f->exec_ctx.stack = fiber_stack;
    f->create_attr = *attr;
    f->self_memblk = memblk;

    return 0;
}

void monad_fiber_destroy(monad_fiber_t *fiber)
{
    MONAD_ASSERT(fiber != nullptr);
    dealloc_fiber_stack(fiber->exec_ctx.stack);
    monad_cma_dealloc(fiber->create_attr.alloc, fiber->self_memblk);
}

int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, uintptr_t fdata)
{
    size_t stack_size;

    MONAD_SPINLOCK_LOCK(&fiber->exec_ctx.lock);
    switch (fiber->exec_ctx.state) {
    case MF_STATE_INIT:
        [[fallthrough]];
    case MF_STATE_CAN_RUN:
        [[fallthrough]];
    case MF_STATE_FINISHED:
        // It is legal to modify the fiber in these states
        break;

    default:
        // It is not legal to modify the fiber in these states
        MONAD_SPINLOCK_UNLOCK(&fiber->exec_ctx.lock);
        return EBUSY;
    }
    stack_size =
        fiber->exec_ctx.stack.stack_top - fiber->exec_ctx.stack.stack_bottom;
    fiber->exec_ctx.state = MF_STATE_CAN_RUN;
    fiber->exec_ctx.md_suspended_ctx = monad_make_fcontext(
        fiber->exec_ctx.stack.stack_top, stack_size, fiber_entrypoint);
    fiber->priority = priority;
    fiber->ffunc = ffunc;
    fiber->fdata = fdata;
    ++fiber->exec_ctx.stats.total_reset;
    MONAD_SPINLOCK_UNLOCK(&fiber->exec_ctx.lock);
    return 0;
}

monad_fiber_t *monad_fiber_self()
{
    monad_thread_executor_t *const thr_exec = _monad_current_thread_executor();
    return thr_exec->cur_fiber;
}

int monad_fiber_run(
    monad_fiber_t *next_fiber, monad_fiber_suspend_info_t *suspend_info)
{
    int err;
    struct monad_transfer_t resume_xfer;
    monad_fiber_suspend_info_t next_fiber_suspend_info;
    monad_thread_executor_t *thr_exec;
    struct monad_exec_context *cur_exec;
    struct monad_exec_context *next_exec;

    MONAD_DEBUG_ASSERT(next_fiber != nullptr);
    thr_exec = _monad_current_thread_executor();
    cur_exec = _monad_current_exec_context(thr_exec);
    next_exec = &next_fiber->exec_ctx;

    // The fiber is usually already locked, since fibers remain locked when
    // returned from the run queue. However, you can also run a fiber directly
    // e.g., in the test suite. Acquire the lock if we don't have it
    if (MONAD_UNLIKELY(!monad_spinlock_is_owned(&next_exec->lock))) {
        MONAD_SPINLOCK_LOCK(&next_exec->lock);
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
        MONAD_SPINLOCK_UNLOCK(&next_exec->lock);
        return err;
    }

    MONAD_DEBUG_ASSERT(monad_spinlock_is_unowned(&cur_exec->lock));
    MONAD_SPINLOCK_LOCK(&cur_exec->lock);

    // Switch into next_fiber
    resume_xfer = start_context_switch(
        cur_exec,
        next_exec,
        MF_STATE_EXEC_WAIT,
        MF_SUSPEND_SLEEP,
        (uintptr_t)next_fiber);
    asm volatile("" ::: "memory");
    next_fiber_suspend_info = finish_context_switch(resume_xfer);
    if (suspend_info != nullptr) {
        memcpy(suspend_info, &next_fiber_suspend_info, sizeof *suspend_info);
    }
    return 0;
}

int monad_fiber_get_name(monad_fiber_t *fiber, char *name, size_t size)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(&fiber->exec_ctx.lock);
    rc = strlcpy(name, fiber->name, size) >= size ? ERANGE : 0;
    MONAD_SPINLOCK_UNLOCK(&fiber->exec_ctx.lock);
    return rc;
}

int monad_fiber_set_name(monad_fiber_t *fiber, char const *name)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(&fiber->exec_ctx.lock);
    rc = strlcpy(fiber->name, name, sizeof fiber->name) > MONAD_FIBER_NAME_LEN
             ? ERANGE
             : 0;
    MONAD_SPINLOCK_UNLOCK(&fiber->exec_ctx.lock);
    return rc;
}

void monad_fiber_yield(uintptr_t eval)
{
    monad_thread_executor_t *const thr_exec = _monad_current_thread_executor();
    monad_fiber_t *const self = thr_exec->cur_fiber;
    MONAD_DEBUG_ASSERT(self != nullptr);
    MONAD_SPINLOCK_LOCK(&self->exec_ctx.lock);
    suspend_fiber(&self->exec_ctx, MF_STATE_CAN_RUN, MF_SUSPEND_YIELD, eval);
}
