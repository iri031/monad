#pragma once

#include <monad/fiber/fcontext.h>
#include <monad/fiber/sanitizer.h>
#include <stdbool.h>

#if defined(__cplusplus)
extern "C" {
#endif

#if defined(MONAD_USE_ASAN)
struct monad_fiber_context_asan_fake_stack
{
  void  *fake_stack;
  void  *stack_bottom;
  size_t stack_size;

};
#endif

typedef struct monad_fiber_context {
  fcontext_t fiber;
#if defined(MONAD_USE_TSAN)
  void * tsan_fiber;
#endif

#if defined(MONAD_USE_ASAN)
  struct monad_fiber_context_asan_fake_stack asan, * asan_to_finish;
#endif

  // potential additions: context_local data, unwind code, tracing (for debugging) and names (which could be used with tsan)
  // and we can add a vtable here

  // there is NO exit function at this moment, but we could add this.
  // it's unspecified what happens if you destroy the main context, as it would always be a leak one would assume.
} monad_fiber_context_t;

// are in this fiber at the moment
#define monad_fiber_is_current(This) (This->fiber != NULL)

monad_fiber_context_t * monad_fiber_main_context();

// the return is the context we're resumed from
monad_fiber_context_t * monad_fiber_context_switch(monad_fiber_context_t * from, monad_fiber_context_t * to);
monad_fiber_context_t * monad_fiber_context_switch_with(
                                monad_fiber_context_t * from, monad_fiber_context_t * to,
                                monad_fiber_context_t * (*func)(monad_fiber_context_t*, void*), void* arg);

static const size_t monad_fiber_default_stack_size = 128 * 1024;
monad_fiber_context_t * monad_fiber_context_callcc(
    monad_fiber_context_t * from,
    size_t stack_size, bool protected_stack,
    monad_fiber_context_t * (*func)(void* /* func_arg */, monad_fiber_context_t * /* fiber */ , monad_fiber_context_t * /* from */),
    void * func_arg);


#if defined(__cplusplus)
}
#endif
