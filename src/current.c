#include <monad/fiber/current.h>
#include <monad/fiber/assert.h>
#include <threads.h>


void _main_fiber_resume (struct monad_fiber_task* const this)
{
  monad_fiber_switch_to_fiber((monad_fiber_t* const)this);
}

void _main_fiber_destroy(struct monad_fiber_task* const this)
{
  (void)this;
  pthread_exit(NULL);
}

static thread_local monad_fiber_t _main_fiber = {
    .task = {
        .resume=&_main_fiber_resume,
        .destroy=&_main_fiber_destroy
    },
    .context=NULL,
    .priority=0u,
    .scheduler=NULL
};


monad_fiber_t * monad_fiber_main()
{
  return &_main_fiber;
}

bool monad_fiber_is_main(monad_fiber_t * const this)
{
  return this->task.destroy == _main_fiber_destroy;
}

static thread_local monad_fiber_t * _current = NULL;

monad_fiber_t * monad_fiber_current()
{
  if (_current == NULL)
  {
    _current = &_main_fiber;
    _main_fiber.context = monad_fiber_main_context();
  }
  return _current;
}

monad_fiber_t * activate_fiber(monad_fiber_t * new_current)
{
  monad_fiber_t * pre = monad_fiber_current();
  _current = new_current;
  return pre;
}

void monad_fiber_switch_to_fiber(monad_fiber_t * target)
{
  monad_fiber_t * pre = monad_fiber_current();
  _current = target;

  // LOG here
  (void) monad_fiber_context_switch(pre->context, target->context);
  MONAD_ASSERT(_current == pre); // make sure we switched back through monad_fiber_switch_current_fiber
}

void monad_fiber_switch_to_main()
{
  // LOG here
  monad_fiber_switch_to_fiber(&_main_fiber);
}


static monad_fiber_context_t * monad_fiber_yield_impl(monad_fiber_context_t* from, void* arg_)
{
  monad_fiber_task_t * task = (monad_fiber_task_t*)arg_;
  monad_fiber_t * ctx = monad_fiber_main();
  activate_fiber(ctx);
  task->resume(task);
  return ctx->context;
}

void monad_fiber_yield()
{
  // check
  monad_fiber_t * cc = monad_fiber_current();
  monad_fiber_task_t * t = monad_fiber_scheduler_pop_higher_priority_task(cc->scheduler, cc->priority);
  if (t == NULL)
    return; // not work, no problem

  monad_fiber_context_switch_with(
      cc->context,
      monad_fiber_main_context(),
      &monad_fiber_yield_impl,
      &t);

  activate_fiber(cc);
}

struct monad_fiber_await_impl_t
{
  monad_fiber_t * fiber;
  void (*suspend_to)(
      monad_fiber_t * /*task */,
      void * /*arg*/);
  void * arg;
};

static monad_fiber_context_t * monad_fiber_await_impl(monad_fiber_context_t *from, void *ptr)
{
  struct monad_fiber_await_impl_t impl = *(struct monad_fiber_await_impl_t*)ptr;
  (*impl.suspend_to)(impl.fiber, impl.arg);
  return from;
}

void monad_fiber_await(
    void (*suspend_to)(
        monad_fiber_t * /*task */,
        void * /*arg*/),
    void * arg)
{
  monad_fiber_t *from = monad_fiber_current();
  // Mustn't be called from main context!
  assert(from->context != monad_fiber_main_context());

  struct monad_fiber_await_impl_t impl =
      {
      .fiber=from,
      .suspend_to=suspend_to,
      .arg=arg
      };

  monad_fiber_context_switch_with(
      from->context, monad_fiber_main_context(),
      &monad_fiber_await_impl,
      &impl);
}