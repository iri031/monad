#pragma once

#if defined(__cplusplus)
extern "C" {
#endif


#include <monad/fiber/fcontext.h>
#include <monad/fiber/sanitizer.h>

#include <stddef.h>
#include <stdbool.h>

typedef struct monad_fiber
{
  void (*resume)(struct monad_fiber* const);
  void (*destroy)(struct monad_fiber* const);

  fcontext_t fiber, awaited_from;
  size_t allocated_size;

#if defined(MONAD_USE_TSAN)
  void * tsan_fiber;
#endif

#if defined(MONAD_USE_ASAN)
  void  *asan_fake_stack;
  void  *asan_stack_bottom;
  size_t asan_stack_size;
#endif


  void (*func)(void*, struct monad_fiber *);
  void * func_arg;

  struct _monad_fiber_cleanup_buffer * cleanup_buffer;
} monad_fiber_t;


typedef monad_fiber_t monad_fiber_context_t;

static const size_t monad_fiber_default_stack_size = 128 * 1024;

monad_fiber_t * monad_fiber_create(size_t stack_size, bool protected_, void (*func)(void*, monad_fiber_t *), void * func_arg);
void monad_fiber_resume(monad_fiber_t *);
void monad_fiber_suspend(monad_fiber_t *);

#define monad_fiber_destroy(this) this->destroy(this)
// copied from monad_fiber

/* Cleanup buffers */
struct _monad_fiber_cleanup_buffer
{
  void (*__routine) (void *);             /* Function to call.  */
  void *__arg;                            /* Its argument.  */
  struct _monad_fiber_cleanup_buffer *__prev; /* Chaining of cleanup functions.  */
};


void __monad_fiber_register_cancel  (monad_fiber_t * , struct _monad_fiber_cleanup_buffer * buffer);
void __monad_fiber_unregister_cancel(monad_fiber_t * , struct _monad_fiber_cleanup_buffer * buffer);


# define monad_fiber_cleanup_push(fiber, routine, arg)                        \
  do {									                                      \
    struct __monad_fiber_cleanup_buffer __cancel_buf;				          \
    __cancel_buf.__routine = (routine);			                              \
    __cancel_buf.__arg     = (arg);						                      \
	__monad_fiber_register_cancel (fiber, &__cancel_buf);				      \
    do {


/* Remove a cleanup handler installed by the matching monad_fiber_cleanup_push.
   If EXECUTE is non-zero, the handler function is called. */
# define monad_fiber_cleanup_pop(fiber, execute)                                   \
      do { } while (0);/* Empty to allow label before monad_fiber_cleanup_pop.  */ \
    } while (0);							                                       \
    __monad_fiber_unregister_cancel (fiber, &__cancel_buf);			               \
    if (execute)							                                       \
      __cancel_buf.__routine (__cancel_buf.__arg);					               \
  } while (0)


void fiber_cleanup_push(monad_fiber_t *, void (*routine)(void *), void *arg);
void fiber_cleanup_pop (monad_fiber_t *, bool execute);

#define monad_fiber_done(This) (!This->fiber)

#if defined(__cplusplus)
}
#endif
