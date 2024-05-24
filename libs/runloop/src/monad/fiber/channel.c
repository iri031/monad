#include <monad/fiber/assert.h>
#include <monad/fiber/channel.h>

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

struct monad_fiber_channel_read_op
{
  monad_fiber_t * fiber;
  void * target;

  struct monad_fiber_channel_read_op * next;
};


struct monad_fiber_channel_write_op
{
  monad_fiber_t * fiber;
  const void * source;

  struct monad_fiber_channel_write_op * next;
};

void monad_fiber_channel_create(monad_fiber_channel_t * this, size_t capacity, size_t element_size)
{
  this->capacity = capacity;
  this->size = 0u;
  this->offset = 0u;
  this->element_size = element_size;
  this->pending_reads  = NULL;
  this->pending_writes = NULL;

  MONAD_CCALL_ASSERT(pthread_mutex_init(&this->mutex, NULL));

  if (element_size * capacity > 0)
    this->data = malloc(element_size * capacity);
  else
    this->data = NULL;
}

void monad_fiber_channel_destroy(monad_fiber_channel_t * this)
{
  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

  while (this->pending_writes != NULL)
  {
    struct monad_fiber_channel_write_op *op = this->pending_writes;
    op->source = (void*)UINTPTR_MAX; // indicate cancellation!
    monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task, op->fiber->priority);
    this->pending_writes = op->next;
  }

  while (this->pending_reads != NULL)
  {
    struct monad_fiber_channel_read_op *op = this->pending_reads;
    op->target = (void*)UINTPTR_MAX; // indicate cancellation!
    monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task, op->fiber->priority);
    this->pending_reads = op->next;
  }

  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
  MONAD_CCALL_ASSERT(pthread_mutex_destroy(&this->mutex));
  if (this->data != NULL)
    free(this->data);
}


bool monad_fiber_channel_try_read(monad_fiber_channel_t * this, void * target)
{
  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
  bool has_result = false;

  if (this->pending_writes != NULL)
  {
    struct monad_fiber_channel_write_op * op = this->pending_writes;
    this->pending_writes = op->next;

    if (this->element_size > 0)
      memcpy(target, op->source, this->element_size);

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();

    const int64_t my_priority = current->priority;
    if (op->fiber->priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_scheduler_post(current->scheduler, &current->task, current->priority);
      monad_fiber_switch_to_fiber(op->fiber); // returning
      return true; // early return, to avoid multiple unlocks
    }
    else // post will go fine with locking
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task, op->fiber->priority);

    has_result = true;
    return true; // already unlocked!
  }
  else if (this->size > 0u)
  {
    if (this->element_size == 0u) // zero
      this->size --;
    else
    {
      // pos = offset
      memcpy(target,  ((char*)this->data + (this->element_size * this->offset)), this->element_size);
      this->offset ++;
      this->size --;
      if (this->offset == this->capacity)
        this->offset = 0;
    }
    has_result = true;
  }

  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
  return has_result;
}

bool monad_fiber_channel_try_write(monad_fiber_channel_t * this, const void * source)
{
  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
  bool has_result = false;
  if (this->pending_reads != NULL)
  {
    struct monad_fiber_channel_read_op * op = this->pending_reads;
    this->pending_reads = op->next;

    if (this->element_size > 0)
        memcpy(op->target, source, this->element_size);

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();
    const int64_t my_priority = current->priority;
    if (op->fiber->priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_scheduler_post(current->scheduler, &current->task, current->priority);
      monad_fiber_switch_to_fiber(op->fiber); // returning
      return true; // early return, to avoid multiple returns!
    }
    else // post will go fine with locking
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task, op->fiber->priority);

    has_result = true;

    return true;
  }
  else if (this->size < this->capacity)
  {
    if (this->element_size == 0u)
      this->size++;
    else
    {
      memcpy(((char*)this->data + (this->element_size * this->offset)), source, this->element_size);
      this->size++;
    }
    has_result = true;
  }

  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
  return has_result;
}

static void monad_fiber_await_unlock_impl(monad_fiber_t * task, void * arg)
{
  (void)task;
  MONAD_CCALL_ASSERT(pthread_mutex_unlock(((pthread_mutex_t*)arg)));
}



int monad_fiber_channel_read(monad_fiber_channel_t * this, void * target)
{
  if (target == (void*)UINTPTR_MAX)
    target = NULL;

  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

  if (this->pending_writes != NULL)
  {
    struct monad_fiber_channel_write_op * op = this->pending_writes;
    this->pending_writes = op->next;

    if (this->element_size > 0)
      memcpy(target, op->source, this->element_size);

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();

    const int64_t my_priority = current->priority;
    if (op->fiber->priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_scheduler_post(current->scheduler, &current->task, current->priority);
      monad_fiber_switch_to_fiber(op->fiber); // returning
      return true; // early return, to avoid multiple unlocks
    }
    else // post will go fine with locking
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task, op->fiber->priority);

    return 0; // already unlocked!
  }
  else if (this->size > 0u)
  {
    if (this->element_size == 0u) // zero
      this->size --;
    else
    {
      // pos = offset
      memcpy(target,  ((char*)this->data + (this->element_size * this->offset)), this->element_size);
      this->offset ++;
      this->size --;
      if (this->offset == this->capacity)
        this->offset = 0;
    }
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return 0;
  }
  else // nothing available, let's suspend
  {
    // ask james if this should be prioritized.
    struct monad_fiber_channel_read_op my_op = {.fiber=monad_fiber_current(), .target = target, .next = NULL};
    struct monad_fiber_channel_read_op * op = this->pending_reads;
    if (op == NULL) // insert directly
      this->pending_reads = &my_op;
    else
    {
      while (op->next != NULL)
        op = op->next;
      op->next = &my_op;
    }
    // ok, set up, not suspend and unlock after suspending -> before is a race condition
    monad_fiber_await(&monad_fiber_await_unlock_impl, (void*)&this->mutex);

    if (op->target == (void*)UINTPTR_MAX)
      return EPIPE;
  }

  return 0;

}

int monad_fiber_channel_write(monad_fiber_channel_t * this, const void * source)
{
  if (source == (const void*)UINTPTR_MAX)
    source = NULL;

  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

  if (this->pending_reads != NULL)
  {
    struct monad_fiber_channel_read_op * op = this->pending_reads;
    this->pending_reads = op->next;

    if (this->element_size > 0)
      memcpy(op->target, source, this->element_size);

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();
    const int64_t my_priority = current->priority;
    if (op->fiber->priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_scheduler_post(current->scheduler, &current->task, current->priority);
      monad_fiber_switch_to_fiber(op->fiber); // returning
      return true; // early return, to avoid multiple returns!
    }
    else // post will go fine with locking
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task, op->fiber->priority);

    return 0;
  }
  else if (this->size < this->capacity)
  {
    if (this->element_size == 0u)
      this->size++;
    else
    {
      memcpy(((char*)this->data + (this->element_size * this->offset)), source, this->element_size);
      this->size++;
    }

    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return 0;
  }
  else // nothing available, let's suspend
  {
    // ask james if this should be prioritized.
    struct monad_fiber_channel_write_op my_op = {.fiber=monad_fiber_current(), .source = source, .next = NULL};
    struct monad_fiber_channel_write_op * op = this->pending_writes;
    if (op == NULL) // insert directly
      this->pending_writes = &my_op;
    else
    {
      while (op->next != NULL)
        op = op->next;
      op->next = &my_op;
    }
    // ok, set up, not suspend and unlock after suspending -> before is a race condition
    monad_fiber_await(&monad_fiber_await_unlock_impl, (void*)&this->mutex);

    if (op->source == (void*)UINTPTR_MAX)
      return EPIPE;
  }
  return 0;
}

