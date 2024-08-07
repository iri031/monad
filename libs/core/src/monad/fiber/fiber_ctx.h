#pragma once

/*
 * @file
 *
 * This file contains declarations of structures and functions from Boost
 * context. We don't include the Boost headers directly, since they are C++
 * headers. We only need to link to two C-linkage functions, namely the
 * machine-dependent fiber switch functions, which are implemented in assembly.
 * These functions are not extern "C", as this is not a public header and
 * should only be included by pure C code.
 */

#include <stddef.h>

typedef void *monad_fiber_ctx_t;
typedef struct monad_fiber monad_fiber_t;

// Encapsulates the information needed to transfer back to the context that
// just transferred control to us; must match the transfer_t structure layout
// from the file `context/detail/fcontext.hpp`
typedef struct monad_fiber_transfer {
    monad_fiber_ctx_t prev_fctx;
    monad_fiber_t *prev_fiber;
} monad_fiber_transfer_t;

// Make a new fiber context. This constructs a dummy stack frame rooted at
// `stack_pointer` which serves as the parent frame of the fiber function.
// The fiber function cannot return since the dummy frame has nowhere to return
// to (it will call exit(3) if the fiber function returns to it)
extern monad_fiber_ctx_t make_fcontext(void *stack_pointer, size_t size,
                                       void (*fiber_fn)(monad_fiber_transfer_t));

// Jump to the given fiber context, passing in the data pointer. This runs the
// fiber until it suspends for some reason, and returns the
// monad_fiber_transfer_t that will enable us to resume at the suspension point
extern monad_fiber_transfer_t jump_fcontext(monad_fiber_ctx_t to, void *vp);