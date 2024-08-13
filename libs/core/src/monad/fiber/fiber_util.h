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

#include <monad/core/dump.h>
#include <monad/fiber/fiber.h>

#ifdef __cplusplus
extern "C" {
#endif

/// Given a fiber stack and the suspended context of the fiber, return the
/// remaining stack space
static inline size_t monad_fiber_get_free_stack_space(monad_fiber_stack_t stack,
                                                      monad_fcontext_t ctx) {
    return (size_t)((const uint8_t*)ctx - (const uint8_t*)stack.stack_bottom);
}

/// Given a fiber stack and the suspended context of the fiber, return the used
/// stack space
static inline size_t monad_fiber_get_used_stack_space(monad_fiber_stack_t stack,
                                                      monad_fcontext_t ctx) {
    return (size_t)((const uint8_t*)stack.stack_top - (const uint8_t*)ctx);
}

/// Helper function to allocates a fixed-size stack; the last page in the stack
/// will have all of its permissions removed, to serve as a guard page; the
/// reduced stack size is also returned via the stack_size parameter
int monad_fiber_alloc_stack(size_t *stack_size, monad_fiber_stack_t *stack);

/// Frees a stack allocated by an earlier call to monad_fiber_alloc_stack
void monad_fiber_free_stack(monad_fiber_stack_t stack);

/// Dump debugging info about a fiber
void monad_fiber_dump(const monad_fiber_t *fiber, monad_dump_ctx_t *fiber_ctx);

/// Add a fiber to a global list of all fibers, so information about it can be
/// dumped if the application crashes
void monad_fiber_debug_add(monad_fiber_t *fiber);

/// All fibers for which we call monad_fiber_debug_add must call this function
/// before the fiber memory is deallocated
void monad_fiber_debug_remove(monad_fiber_t *fiber);

/// Dump all info about fibers that were added with monad_fiber_debug_add
void monad_fiber_debug_dump_all(monad_dump_ctx_t *all_fibers_ctx);

/// A function that will dump fiber information when a signal is received; has
/// the signature of a `sa_sigaction` callback from sigaction(2)
void monad_fiber_debug_sigaction(int signo, siginfo_t *siginfo, void *ucontext);

#ifdef __cplusplus
} // extern "C"
#endif
