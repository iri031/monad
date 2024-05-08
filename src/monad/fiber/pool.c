#include <monad/fiber/assert.h>
#include <monad/fiber/current.h>
#include <monad/fiber/pool.h>

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

static void monad_fiber_pool_impl_resume(monad_fiber_task_t * task)
{
  monad_fiber_switch_to_fiber((monad_fiber_t*)task);
}




monad_fiber_context_t * monad_fiber_pool_impl(void* arg,
                                              monad_fiber_context_t * fiber,
                                              monad_fiber_context_t * from)
{
    monad_fiber_pooled_t * const this = (monad_fiber_pooled_t  *)arg;

    struct monad_fiber_task_node task_node = {NULL, 0u};

    if (setjmp(this->exit_jmp))
        return from; // this should be main, but a kind of scheduler either way.

    monad_fiber_pool_t * pool = this->pool;

    char name[24];
    snprintf(name, 24, "worker fiber %u", ++(pool->fiber_id_source));
    monad_fiber_set_name(fiber, name);


    monad_fiber_context_switch(this->fiber.context, from);
    MONAD_ASSERT(monad_fiber_is_current(fiber));
    // beyond here, we need some handling of the *current*
    while (true)
    {
        this->fiber.priority = INT64_MIN;
        monad_fiber_channel_read(&pool->queue_semaphore, NULL);
        // suspend here and wait for a task

        while (task_node.task != NULL)
        {
          MONAD_CCALL_ASSERT(pthread_mutex_lock(&pool->queue_mutex));

          if (pool->queue.size > 0u)
            task_node = monad_fiber_task_queue_pop_front(&pool->queue);
          else
            task_node.task = NULL;

          MONAD_CCALL_ASSERT(pthread_mutex_unlock(&pool->queue_mutex));
          if (task_node.task == NULL)
            monad_fiber_yield(); // this SHOULD be unnecessary
        }

        this->fiber.priority = task_node.priority;
        task_node.task->resume(task_node.task);

    }
}


monad_fiber_context_t * monad_fiber_pool_destroy_destroy_fiber(monad_fiber_context_t* this, void* arg_)
{
  monad_fiber_pooled_t * const arg = (monad_fiber_pooled_t * )arg_;
  if (arg->current_task != NULL)
    arg->current_task->destroy(arg->current_task);
  longjmp(arg->exit_jmp, 1);
  (void)this;
}

static void monad_fiber_pool_impl_destroy(struct monad_fiber_task *const task)
{
  monad_fiber_t * t =(monad_fiber_t*)task;
  monad_fiber_pool_destroy_destroy_fiber(t->context, task);
}


void monad_fiber_pool_create  (monad_fiber_pool_t * this, size_t fibers)
{
  this->fibers_data = malloc(sizeof(monad_fiber_pooled_t) * fibers);
  this->fibers_size = fibers;

  memset(this->fibers_data, (int)fibers, sizeof(monad_fiber_pooled_t));

  for (size_t i = 0; i < fibers; i++)
  {
    monad_fiber_pooled_t *f = &this->fibers_data[i];
    f->current_task = NULL;
    f->idle = false;
    f->pool = this;
    f->fiber.task.resume  = &monad_fiber_pool_impl_resume;
    f->fiber.task.destroy = monad_fiber_pool_impl_destroy;
    f->fiber.scheduler = monad_fiber_scheduler_current();
    f->fiber.context= monad_fiber_context_callcc(
                  monad_fiber_main_context(),
                  true,
                  monad_fiber_default_stack_size,
                  &monad_fiber_pool_impl,
                  f);
  }

  monad_fiber_task_queue_init(&this->queue);
  MONAD_CCALL_ASSERT(pthread_mutex_init(&this->queue_mutex, NULL));
  this->fiber_id_source  = 1;
  monad_fiber_channel_create(&this->queue_semaphore, SIZE_MAX, 0u);
}


void monad_fiber_pool_destroy (monad_fiber_pool_t * this)
{
  for (size_t i = 0u; i < this->fibers_size; i++)
  {
    monad_fiber_pooled_t * fiber = &this->fibers_data[i];
    monad_fiber_context_switch_with(
        monad_fiber_main_context(), // replace with current!
        fiber->fiber.context,
        &monad_fiber_pool_destroy_destroy_fiber,
        fiber);
  }

  free(this->fibers_data);
  monad_fiber_task_queue_destroy(&this->queue);
}

void monad_fiber_pool_run     (monad_fiber_pool_t * this, monad_fiber_task_t * task, int64_t priority)
{
  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->queue_mutex)); // insert the task
  monad_fiber_task_queue_insert(&this->queue, task, priority);
  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->queue_mutex));
  monad_fiber_channel_write(&this->queue_semaphore, NULL);
}
