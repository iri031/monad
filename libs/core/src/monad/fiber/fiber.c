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
#include <monad/fiber/fiber.h>

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
    (void)_monad_finish_context_switch(xfer_from);
    self = monad_fiber_self();

    // Call the user fiber function
    rc = self->ffunc(self->fdata);

    // The fiber function returned, which appears as a kind of suspension to
    // the caller
    MONAD_SPINLOCK_LOCK(&self->lock);
    _monad_suspend_fiber(self, MF_STATE_FINISHED, MF_SUSPEND_RETURN, rc);

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
    rc = monad_cma_alloc(
        attr->alloc, sizeof **fiber, alignof(monad_fiber_t), &memblk);
    if (rc != 0) {
        dealloc_fiber_stack(fiber_stack);
        return rc;
    }
    *fiber = f = memblk.ptr;
    memset(f, 0, sizeof *f);
    monad_spinlock_init(&f->lock);
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

    MONAD_SPINLOCK_LOCK(&fiber->lock);
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
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return EBUSY;
    }
    stack_size =
        fiber->exec_ctx.stack.stack_top - fiber->exec_ctx.stack.stack_bottom;
    fiber->exec_ctx.state = MF_STATE_CAN_RUN;
    fiber->exec_ctx.md_suspended_ctx = monad_make_fcontext(
        fiber->exec_ctx.stack.stack_top, stack_size, fiber_entrypoint);
    fiber->exec_ctx.stats = &fiber->stats;
    fiber->priority = priority;
    fiber->ffunc = ffunc;
    fiber->fdata = fdata;
    ++fiber->stats.total_reset;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return 0;
}

int monad_fiber_get_name(monad_fiber_t *fiber, char *name, size_t size)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    rc = strlcpy(name, fiber->name, size) >= size ? ERANGE : 0;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return rc;
}

int monad_fiber_set_name(monad_fiber_t *fiber, char const *name)
{
    int rc;
    if (name == nullptr) {
        return EFAULT;
    }
    MONAD_SPINLOCK_LOCK(&fiber->lock);
    rc = strlcpy(fiber->name, name, sizeof fiber->name) > MONAD_FIBER_NAME_LEN
             ? ERANGE
             : 0;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return rc;
}
