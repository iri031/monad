#include <monad/fiber/fiber.h>
#include <malloc.h>
#include <sys/resource.h>
#include <unistd.h>
#include <sys/mman.h>

#include <monad/fiber/fcontext.h>

#if defined(MONAD_USE_TSAN)
#include <sanitizer/tsan_interface.h>
#endif

#if defined(MONAD_USE_ASAN)
#include  <sanitizer/asan_interface.h>
#endif

#include <unwind.h>

static struct transfer_t self_destroy_impl(struct transfer_t t)
{
  struct transfer_t n = {NULL, t.data};
  return n;
}

static void __attribute__((noinline)) monad_fiber_impl(struct transfer_t t)
{
  monad_fiber_t * this = (monad_fiber_t*)t.data;

#if defined(MONAD_USE_ASAN)
  __sanitizer_finish_switch_fiber( (this->fiber == NULL) ?  NULL : this->asan_fake_stack,
                                   (const void **) & this->asan_stack_bottom,
                                   & this->asan_stack_size);
#endif
  
  this->awaited_from = t.fctx;



  this->func(this->func_arg, this);

#if defined(MONAD_USE_ASAN)
  __sanitizer_start_switch_fiber( & this->asan_fake_stack, this->asan_stack_bottom, this->asan_stack_size);
#endif

  ontop_fcontext(this->awaited_from, this, &self_destroy_impl);
  //
}

_Unwind_Reason_Code monad_fiber_unwind_stop_function(
    int c, _Unwind_Action a, _Unwind_Exception_Class cl, struct _Unwind_Exception * ex,
        struct _Unwind_Context * ctx, fcontext_t outer)
{
  (void)c;
  (void)a;
  (void)cl;
  (void)ex;

  void *ff =  _Unwind_FindEnclosingFunction((void*)_Unwind_GetIP(ctx));
  if (ff == &monad_fiber_impl)
    jump_fcontext(outer, NULL);

  return _URC_NO_REASON;
}

static struct transfer_t monad_fiber_unwind_impl(struct transfer_t t)
{
  //run the cleanup first - TODO: Check if this can be moved into the unwind code
  monad_fiber_t * this = (monad_fiber_t*)(t.data);
  for (struct _monad_fiber_cleanup_buffer * buf = this->cleanup_buffer;
       buf  != NULL; buf = buf->__prev)
    buf->__routine(buf->__arg);

  static struct _Unwind_Exception dummy_exception;
  _Unwind_ForcedUnwind(&dummy_exception, monad_fiber_unwind_stop_function, t.fctx);
  return t;
}


static void monad_fiber_unwind(monad_fiber_t * this)
{
  if (this->fiber)
  {
#if defined(MONAD_USE_TSAN)
    void * const f = __tsan_get_current_fiber();
    __tsan_switch_to_fiber(this->tsan_fiber, 0);
#endif
    ontop_fcontext(this->fiber, this, &monad_fiber_unwind_impl);
#if defined(MONAD_USE_TSAN)
    __tsan_switch_to_fiber(f, 0);
#endif
  }
}

static void monad_fiber_destroy_(monad_fiber_t * this)
{
#if defined(BOOST_USE_TSAN)
  f(this->tsan_fiber);
#endif
}

static void monad_fiber_delete_protected(monad_fiber_t * this)
{
  monad_fiber_unwind(this);
  monad_fiber_destroy_(this);
  munmap((char*)this + sizeof(monad_fiber_t) - this->allocated_size, this->allocated_size);
}
static void monad_fiber_delete_raw(monad_fiber_t * this)
{
  monad_fiber_unwind(this);
  monad_fiber_destroy_(this);
  free((char*)this + sizeof(monad_fiber_t)  - this->allocated_size);
}

void monad_fiber_resume(monad_fiber_t * this)
{

#if defined(MONAD_USE_ASAN)
  __sanitizer_start_switch_fiber( & this->asan_fake_stack, this->asan_stack_bottom, this->asan_stack_size);
#endif

#if defined(MONAD_USE_TSAN)
  void * f = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(this->tsan_fiber, 0);
#endif

  struct transfer_t t = jump_fcontext(this->fiber, this);
  // in a chain of resumptions this might point to another coro!
  this = (monad_fiber_t *)t.data;

#if defined(MONAD_USE_TSAN)
  __tsan_switch_to_fiber(f, 0);
#endif

#if defined(MONAD_USE_ASAN)
  __sanitizer_finish_switch_fiber( (this->fiber == NULL) ?  NULL : this->asan_fake_stack,
                                   (const void **) & this->asan_stack_bottom,
                                   & this->asan_stack_size);
#endif
  this->fiber = t.fctx;
}


monad_fiber_t * monad_fiber_create(size_t stack_size, bool protected,
                                   void (*func)(void*, monad_fiber_t *), void * func_arg)
{
  void * memory = NULL;
  size_t allocated_size = stack_size;
  if (protected)
  {
    // taken from boost.context
    const size_t page_size = sysconf( _SC_PAGESIZE);
    const size_t pages = (stack_size + page_size - 1) / page_size;
    allocated_size = (pages + 1) * page_size;

#if defined(MAP_ANON)
    memory = mmap( 0, allocated_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
#else
    memory = mmap( 0, size__, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
#endif
    mprotect( memory, page_size, PROT_NONE);
  }
  else
    memory = malloc(stack_size);

  // | ... <- stack | monad_fiber_t |
  void * sp = ((char*)memory + stack_size) - sizeof(monad_fiber_t );
  monad_fiber_t * fb = (monad_fiber_t*)sp;

  fb->awaited_from = NULL;
  fb->resume  = &monad_fiber_resume;
  fb->destroy = protected ?  &monad_fiber_delete_protected : &monad_fiber_delete_raw;
  fb->allocated_size = allocated_size;
  fb->func = func;
  fb->func_arg = func_arg;

  fb->fiber = make_fcontext(sp, stack_size - sizeof(monad_fiber_t), &monad_fiber_impl);

  fb->cleanup_buffer = NULL;

#if defined(MONAD_USE_TSAN)
  fb->tsan_fiber = __tsan_create_fiber(0);
#endif

#if defined(MONAD_USE_ASAN)
  fb->asan_fake_stack = NULL;
  fb->asan_stack_bottom = NULL;
  fb->asan_stack_size = 0u;
#endif

  return fb;
}

void __monad_fiber_register_cancel  (monad_fiber_t *this , struct _monad_fiber_cleanup_buffer * buffer)
{
  buffer->__prev = this->cleanup_buffer;
  this->cleanup_buffer = buffer;
}

void __monad_fiber_unregister_cancel(monad_fiber_t *this , struct _monad_fiber_cleanup_buffer * buffer)
{
  //MONAD_DEBUG_ASSERT(this->cleanup_buffer == buffer)
  this->cleanup_buffer = buffer->__prev;
}

void monad_fiber_suspend(monad_fiber_t * this)
{
  struct transfer_t t = jump_fcontext(this->awaited_from, this);
  this->awaited_from = t.fctx;
}
