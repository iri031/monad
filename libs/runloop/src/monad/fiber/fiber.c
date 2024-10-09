/**
 * @file
 *
 * This file contains the implementation of the performance-insensitive
 * functions in the fiber library
 */

#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <monad/core/assert.h>
#include <monad/core/c_result.h>
#include <monad/core/likely.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>

#include <monad/context/context_switcher.h>

static monad_fiber_attr_t g_default_fiber_attr = {
    .stack_size = 0,  // Zero uses default size from monad_context_c
    .alloc = nullptr  // Default allocator
};

static monad_c_result fiber_entrypoint(monad_context_task task)
{
    monad_fiber_t *self = (monad_fiber_t *)task;
    _monad_finish_switch_to_fiber(self);
    return self->ffunc(self->fargs);
}

static void fiber_detach(monad_context_task task)
{
    // This function by the `monad_context_c` library is called after
    // `fiber_entrypoint` returns
    monad_context_switcher switcher;
    monad_thread_executor_t *thr_exec;
    monad_fiber_t *const self = (monad_fiber_t *)task;

    MONAD_SPINLOCK_LOCK(&self->lock);
    self->state = MF_STATE_FINISHED;
    switcher = atomic_load_explicit(
        &self->head.context->switcher, memory_order_relaxed);
    thr_exec = switcher->user_ptr;
    thr_exec->suspend_info.suspend_type = MF_SUSPEND_RETURN;
    thr_exec->suspend_info.eval = task->result;
}

static void (*const FIBER_DETACH_ADDR)(monad_context_task) = fiber_detach;

int monad_fiber_create(monad_fiber_attr_t const *attr, monad_fiber_t **fiber)
{
    monad_memblk_t memblk;
    monad_fiber_t *f;
    int rc;

    if (fiber == nullptr) {
        return EFAULT;
    }
    *fiber = nullptr;
    if (attr == nullptr) {
        attr = &g_default_fiber_attr;
    }
    rc = monad_cma_alloc(
        attr->alloc,
        MONAD_CONTEXT_TASK_ALLOCATION_SIZE,
        alignof(monad_fiber_t),
        &memblk);
    if (rc != 0) {
        return rc;
    }
    *fiber = f = memblk.ptr;
    memset(f, 0, sizeof *f);
    monad_spinlock_init(&f->lock);
    f->state = MF_STATE_INIT;
    f->create_attr = *attr;
    f->self_memblk = memblk;

    return 0;
}

void monad_fiber_destroy(monad_fiber_t *fiber)
{
    monad_context_switcher switcher = nullptr;
    MONAD_ASSERT(fiber != nullptr);
    if (fiber->head.context != nullptr) {
        switcher = atomic_load_explicit(
            &fiber->head.context->switcher, memory_order_acquire);
        switcher->destroy(fiber->head.context);
    }
    monad_cma_dealloc(fiber->create_attr.alloc, fiber->self_memblk);
}

int monad_fiber_set_function(
    monad_fiber_t *fiber, monad_fiber_prio_t priority,
    monad_fiber_ffunc_t *ffunc, monad_fiber_args_t fargs)
{
    monad_c_result mcr;
    struct monad_context_task_attr const task_attr = {
        .stack_size = fiber->create_attr.stack_size};
    monad_thread_executor_t *const thr_exec = _monad_current_thread_executor();

    MONAD_SPINLOCK_LOCK(&fiber->lock);
    switch (fiber->state) {
    case MF_STATE_INIT:
        [[fallthrough]];
    case MF_STATE_FINISHED:
        // It is legal to modify the fiber in these states
        break;

    default:
        // It is not legal to modify the fiber in these states
        MONAD_SPINLOCK_UNLOCK(&fiber->lock);
        return EBUSY;
    }

    if (fiber->head.context == nullptr) {
        // The fiber has no associated switchable state (i.e., it has no stack).
        // Tell the switcher to create one.
        mcr = thr_exec->switcher->create(
            &fiber->head.context, thr_exec->switcher, &fiber->head, &task_attr);
        if (MONAD_FAILED(mcr)) {
            MONAD_SPINLOCK_UNLOCK(&fiber->lock);
            return mcr.error.value;
        }
        fiber->head.user_code = fiber_entrypoint;
        fiber->head.user_ptr = nullptr; // XXX: useful somehow?
        memcpy(
            (void *)&fiber->head.detach,
            &FIBER_DETACH_ADDR,
            sizeof fiber->head.detach);
    }

    fiber->state = MF_STATE_CAN_RUN;
    fiber->priority = priority;
    fiber->ffunc = ffunc;
    fiber->fargs = fargs;
    ++fiber->stats.total_reset;
    MONAD_SPINLOCK_UNLOCK(&fiber->lock);
    return 0;
}

void monad_fiber_suspend_save_detach_and_invoke(
    monad_fiber_t *fiber, monad_fiber_t *save,
    bool (*to_invoke)(monad_context_task detached_task))
{
    memcpy(
        ((char *)save) + sizeof(struct monad_context_task_head),
        ((char *)fiber) + sizeof(struct monad_context_task_head),
        sizeof(monad_fiber_t) - sizeof(struct monad_context_task_head));
    monad_context_task context_task = &fiber->head;
    monad_context_switcher switcher = atomic_load_explicit(
        &context_task->context->switcher, memory_order_acquire);
    monad_thread_executor_t *thr_exec =
        (monad_thread_executor_t *)switcher->user_ptr;
    context_task->detach(context_task);
    // Return to base
    thr_exec->call_after_suspend_to_executor = to_invoke;
    switcher->suspend_and_call_resume(context_task->context, nullptr);
}

monad_fiber_t *monad_fiber_from_foreign_context(
    monad_context_task context_task, monad_fiber_t const *save)
{
    monad_fiber_t *fiber = (monad_fiber_t *)context_task;
    memcpy(
        ((char *)fiber) + sizeof(struct monad_context_task_head),
        ((char *)save) + sizeof(struct monad_context_task_head),
        sizeof(monad_fiber_t) - sizeof(struct monad_context_task_head));
    return fiber;
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
