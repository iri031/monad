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
  MONAD_CCALL_ASSERT(pthread_mutex_destroy(&this->mutex));
}

void monad_fiber_channel_close(monad_fiber_channel_t * this)
{
  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

  while (this->pending_writes != NULL)
  {
    struct monad_fiber_channel_write_op *op = this->pending_writes;
    op->source = (void*)UINTPTR_MAX; // indicate cancellation!
    monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task);
    this->pending_writes = op->next;
  }

  while (this->pending_reads != NULL)
  {
    struct monad_fiber_channel_read_op *op = this->pending_reads;
    op->target = (void*)UINTPTR_MAX; // indicate cancellation!
    monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task);
    this->pending_reads = op->next;
  }

  if (this->data != NULL)
  {
    free(this->data);
    this->data = (void*)UINTPTR_MAX;
  }

  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
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
    {
        // pop a value from the buffer and push it into the buffer
        MONAD_DEBUG_ASSERT(this->size == this->capacity);
        if (this->capacity == 0u)
        {
          memcpy(target, op->source, this->element_size);
        }
        else
        {
          memcpy(target,  ((char*)this->data + (this->element_size * this->offset)), this->element_size);
          memcpy(((char*)this->data + (this->element_size * this->offset)), op->source, this->element_size);
        }


        this->offset ++ ; // move the ring buffer around
        if (this->offset == this->capacity)
          this->offset = 0;
    }

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();

    const int64_t my_priority = current->task.priority;
    if (op->fiber->task.priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_scheduler_post(current->scheduler, &current->task);
      monad_fiber_switch_to_fiber(op->fiber); // returning
    }
    else // post will go fine with locking
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task);

    return true; // already unlocked!
  }
  else if (this->size > 0u)
  {
    if (this->element_size != 0u) // zero
    {
      // pos = offset
      memcpy(target,  ((char*)this->data + (this->element_size * this->offset)), this->element_size);
      this->offset ++;
      if (this->offset == this->capacity)
        this->offset = 0;
    }

    this->size --;
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
    const int64_t my_priority = current->task.priority;
    if (op->fiber->task.priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_scheduler_post(current->scheduler, &current->task);
      monad_fiber_switch_to_fiber(op->fiber); // returning
      return true; // early return, to avoid multiple returns!
    }
    else // post will go fine with locking
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task);

    has_result = true;

    return true;
  }
  else if (this->size < this->capacity)
  {
    if (this->element_size != 0u)
    {
      const size_t pos = (this->offset + this->size) % this->capacity;
      memcpy(((char*)this->data + (this->element_size * pos)), source, this->element_size);
    }
    this->size++;
    has_result = true;
  }

  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
  return has_result;
}

struct monad_fiber_await_suspend_read_args
{
  monad_fiber_channel_t * this;
  struct monad_fiber_channel_read_op * op_target;
};

static void monad_fiber_await_read_impl(monad_fiber_t * task, void * arg)
{
  struct monad_fiber_await_suspend_read_args * args =
      (struct monad_fiber_await_suspend_read_args *)arg;

  args->op_target->fiber = task;
  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&args->this->mutex));
}


struct monad_fiber_await_suspend_write_args
{
  monad_fiber_channel_t * this;
  struct monad_fiber_channel_write_op * op_target;
};

static void monad_fiber_await_write_impl(monad_fiber_t * task, void * arg)
{
  struct monad_fiber_await_suspend_write_args * args =
      (struct monad_fiber_await_suspend_write_args *)arg;

  args->op_target->fiber = task;
  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&args->this->mutex));
}

void monad_fiber_channel_post_current(void * fb_)
{
  monad_fiber_t * fiber = (monad_fiber_t*)fb_;
  monad_fiber_scheduler_post(fiber->scheduler, &fiber->task);
}

int monad_fiber_channel_read(monad_fiber_channel_t * this, void * target)
{
  if (target == (void*)UINTPTR_MAX)
    target = NULL;

  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
  if (this->data == (void*)UINTPTR_MAX)
  {
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return EPIPE;
  }

  if (this->pending_writes != NULL)
  {
    struct monad_fiber_channel_write_op * op = this->pending_writes;
    this->pending_writes = op->next;

    if (this->element_size > 0)
    {
        // pop a value from the buffer and push it into the buffer
        MONAD_DEBUG_ASSERT(this->size == this->capacity);
        memcpy(target,  ((char*)this->data + (this->element_size * this->offset)), this->element_size);
        memcpy(((char*)this->data + (this->element_size * this->offset)), op->source, this->element_size);

        this->offset ++ ; // move the ring buffer around
        if (this->offset == this->capacity)
          this->offset = 0;
    }

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();

    const int64_t my_priority = current->task.priority;
    if (op->fiber->task.priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_switch_to_fiber_with(
          op->fiber, &monad_fiber_channel_post_current, current);
    }
    else // post the op for completion. value's in already.
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task);

    return 0; // already unlocked!
  }
  else if (this->size > 0u)
  {
    if (this->element_size != 0u) // not void
    {
      // pos = offset
      memcpy(target,  ((char*)this->data + (this->element_size * this->offset)), this->element_size);
      this->offset ++;
      if (this->offset == this->capacity)
        this->offset = 0;
    }
    this->size --;

    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return 0;
  }
  else // nothing available, let's suspend
  {
    // ask james if this should be prioritized
    struct monad_fiber_channel_read_op my_op = {.fiber=monad_fiber_current(), .target = target, .next = NULL};
    struct monad_fiber_channel_read_op * op = this->pending_reads;
    if (op == NULL) // insert directly
      this->pending_reads = op = &my_op;
    else
    {
      while (op->next != NULL)
        op = op->next;
      op = op->next = &my_op;
    }

    // ok, set up, now suspend and unlock after suspending and get the fiber from the suspended
    struct monad_fiber_await_suspend_read_args arg= {.this=this, .op_target = op };
    monad_fiber_await(&monad_fiber_await_read_impl, (void*)&arg);

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
  if (this->data == (void*)UINTPTR_MAX)
  {
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return EPIPE;
  }

  if (this->pending_reads != NULL)
  {
    struct monad_fiber_channel_read_op * op = this->pending_reads;
    this->pending_reads = op->next;

    if (this->element_size > 0)
      memcpy(op->target, source, this->element_size);

    // unlock here, we already grabbed all from `this`
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));

    monad_fiber_t * current = monad_fiber_current();
    const int64_t my_priority = current->task.priority;
    if (op->fiber->task.priority > my_priority &&
        op->fiber->scheduler == current->scheduler)
    {
      MONAD_ASSERT(current->scheduler != NULL);
      monad_fiber_switch_to_fiber_with(
          op->fiber, &monad_fiber_channel_post_current, current);
    }
    else
    {
      monad_fiber_scheduler_post(op->fiber->scheduler, &op->fiber->task);
    }

    return 0;
  }
  else if (this->size < this->capacity)
  {
    if (this->element_size != 0u)
    {
      const size_t pos = (this->offset + this->size) % this->capacity;
      memcpy(((char*)this->data + pos), source, this->element_size);
    }
    this->size++;

    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    return 0;
  }
  else // nothing available, let's suspend
  {
    // ask james if this should be prioritized.
    struct monad_fiber_channel_write_op my_op = {.fiber=monad_fiber_current(), .source = source, .next = NULL};
    struct monad_fiber_channel_write_op * op = this->pending_writes;
    if (op == NULL) // insert directly
      this->pending_writes = op = &my_op;
    else
    {
      while (op->next != NULL)
        op = op->next;
      op = op->next = &my_op;
    }

    // ok, set up, now suspend and unlock after suspending and get the fiber from the suspended
    struct monad_fiber_await_suspend_write_args arg= {.this=this, .op_target = op };
    monad_fiber_await(&monad_fiber_await_write_impl, (void*)&arg);

    if (op->source == (void*)UINTPTR_MAX)
      return EPIPE;
  }
  return 0;
}

