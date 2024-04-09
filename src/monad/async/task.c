#include "task_impl.h" // MUST BE FIRST INCLUDE

#include "monad/async/task.h"

#include <errno.h>
#include <stdlib.h>

monad_async_result monad_async_task_create(monad_async_task *task, struct monad_async_task_attr *attr)
{
  struct monad_async_task_impl *p = (struct monad_async_task_impl *)calloc(1, sizeof(struct monad_async_task_impl));
  if (p == nullptr)
  {
    return monad_async_make_failure(errno);
  }
  *task = (monad_async_task)p;
  p->head.priority.cpu = monad_async_priority_normal;
  p->head.priority.io = monad_async_priority_normal;
  if (!monad_async_context_init(&p->context, *task, attr))
  {
    monad_async_context_destroy(&p->context);
    (void)monad_async_task_destroy(*task);
    return monad_async_make_failure(errno);
  }
  return monad_async_make_success(0);
}

monad_async_result monad_async_task_destroy(monad_async_task task)
{
  struct monad_async_task_impl *p = (struct monad_async_task_impl *)task;
  monad_async_context_destroy(&p->context);
  free(task);
  return monad_async_make_success(0);
}
