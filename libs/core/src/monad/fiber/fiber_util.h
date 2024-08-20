#pragma once

/**
 * @file
 *
 * This file defines utility functions for monad_fiber_t objects, e.g.,
 * debugging helper functions, convenience functions for allocating stacks,
 * etc.
 */

#include <monad/fiber/fiber.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Helper function to allocates a fixed-size stack; the last page in the stack
/// will have all of its permissions removed, to serve as a guard page; the
/// reduced stack size is also returned via the stack_size parameter
int monad_fiber_alloc_stack(size_t *stack_size, monad_fiber_stack_t *stack);

/// Frees a stack allocated by an earlier call to monad_fiber_alloc_stack
void monad_fiber_free_stack(monad_fiber_stack_t stack);

#ifdef __cplusplus
} // extern "C"
#endif
