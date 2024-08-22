#pragma once

/**
 * @file
 *
 * This file defines utility functions for monad_fiber_t objects, e.g.,
 * debugging helper functions, convenience functions for allocating stacks,
 * etc.
 */

#include <signal.h>
#include <stddef.h>
#include <stdint.h>

#include <monad/fiber/fiber.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Given a fiber stack and the suspended context of the fiber, return the
/// remaining stack space
static inline size_t monad_fiber_get_free_stack_space(
    monad_fiber_stack_t stack, monad_fcontext_t ctx)
{
    return (size_t)((uint8_t const *)ctx - (uint8_t const *)stack.stack_bottom);
}

/// Given a fiber stack and the suspended context of the fiber, return the used
/// stack space
static inline size_t monad_fiber_get_used_stack_space(
    monad_fiber_stack_t stack, monad_fcontext_t ctx)
{
    return (size_t)((uint8_t const *)stack.stack_top - (uint8_t const *)ctx);
}

/// Helper function to allocates a fixed-size stack; the last page in the stack
/// will have all of its permissions removed, to serve as a guard page; the
/// reduced stack size is also returned via the stack_size parameter
int monad_fiber_alloc_stack(size_t *stack_size, monad_fiber_stack_t *stack);

/// Frees a stack allocated by an earlier call to monad_fiber_alloc_stack
void monad_fiber_free_stack(monad_fiber_stack_t stack);

/// Add a fiber to a global list of all fibers, so information about it can be
/// dumped if the application crashes
void monad_fiber_debug_add(monad_fiber_t *fiber);

/// All fibers for which we call monad_fiber_debug_add must call this function
/// before the fiber memory is deallocated
void monad_fiber_debug_remove(monad_fiber_t *fiber);

#ifdef __cplusplus
} // extern "C"
#endif
