#include <monad/fiber/scheduler.h>
#include <pthread.h>

static const size_t monad_fiber_scheduler_task_queue_chunk = 256;

_Thread_local monad_fiber_scheduler_t * monad_fiber_scheduler_current_ = NULL;

monad_fiber_scheduler_t * monad_fiber_scheduler_current() { return monad_fiber_scheduler_current_; }


void monad_fiber_scheduler_task_queue_init(struct monad_fiber_scheduler_task_queue * this)
{
  this->memory = malloc(sizeof(struct monad_fiber_scheduler_task_node) * monad_fiber_scheduler_task_queue_chunk);
  this->capacity = monad_fiber_scheduler_task_queue_chunk;
  this->data = this->memory;
  this->size = 0u;
}

void monad_fiber_scheduler_task_queue_destroy(struct monad_fiber_scheduler_task_queue * this)
{
  free(this->memory);
}

void monad_fiber_scheduler_task_queue_grow(struct monad_fiber_scheduler_task_queue * this)
{
  struct monad_fiber_scheduler_task_node * pre = this->data;
  this->capacity += monad_fiber_scheduler_task_queue_chunk;
  void * new_mem = realloc(this->memory, this->capacity * sizeof(struct monad_fiber_scheduler_task_node));

  MONAD_ASSERT(new_mem != NULL);
  this->memory = new_mem;

  if (this->memory != this->data)
    this->data = this->memory + (this->data - pre);
}


monad_fiber_scheduler_task_t * monad_fiber_scheduler_task_queue_pop_front(struct monad_fiber_scheduler_task_queue * this)
{
  MONAD_ASSERT(this->size > 0ull);
  monad_fiber_scheduler_task_t * t = this->data->task;
  MONAD_ASSERT(t != NULL);

  this->data++;
  this->size--;
  if (this->data == (this->memory + this->capacity))
    this->data = this->memory;

  return t;
}

void monad_fiber_scheduler_task_queue_insert(struct monad_fiber_scheduler_task_queue * this,
                                 monad_fiber_scheduler_task_t * task, size_t priority)
{
  if (this->size == this->capacity) // resize
    monad_fiber_scheduler_task_queue_grow(this);

  struct monad_fiber_scheduler_task_node * itr = this->data,
                                         * end = this->data + this->size;

  if (this->size == 0u)
  {
    this->size ++;
    itr = this->data = this->memory;
    itr->task = task;
    itr->priority = priority;
    return ;
  }

  if (end >= (this->memory + this->capacity))
    end -= this->capacity;

  MONAD_ASSERT(end >= this->memory);

  while (itr != end)
  {
    if (itr->priority <= priority)
      break;

    itr++;
    if (itr == (this->memory + this->capacity))
      itr = this->memory;
  }

  MONAD_ASSERT(itr <= (this->memory + this->capacity));


  if (itr != end) // we need to shift elements right
  {
    if (end < itr) // are we wrapping around the end of the buffer
    {
      struct monad_fiber_scheduler_task_node * mem_end = this->memory + this->capacity;
      // this shifts the lower part (DEF in the below example)

      memmove(this->data + 1, this->data, (end - this->memory) * sizeof(struct monad_fiber_scheduler_task_node));
      if (itr == mem_end) // we're at the end of memory, no need to do a second shift.
      {
        // that's the insert
        // | D | E | F |   |  | A | B | C |
        // | X | D | E | F |  | A | B | C |
        itr = this->memory;
      }
      else
      {

        // | D | E | F |   |   | A | B | C |
        // | C | D | E | F |   | A | X | B |
        this->memory[0] = this->memory[this->capacity - 1]; // wrap one element around (C)
        // move B
        // | C | D | E | F |   | A | X | B |
        //                           ^ itr   ^ mem_end
        memmove(itr + 1, itr, ((mem_end  - itr) - 1) * sizeof(struct monad_fiber_scheduler_task_node));
      }
    }
    else
      memmove(itr+1, itr, (end - itr) * sizeof(struct monad_fiber_scheduler_task_node));

  }
  itr->task = task;
  itr->priority = priority;
  this->size++;
}

extern int pthread_setname_np(pthread_t self, char *name);

static void* work(void * this_)
{
  monad_fiber_scheduler_t *this = (monad_fiber_scheduler_t *) this_;
  char name[16];
  snprintf(name, 16, "worker %u", ++(this->thread_id_source));
  MONAD_CCALL_ASSERT(pthread_setname_np(pthread_self(), name));

  monad_fiber_scheduler_work(this);
  return NULL;
}



void monad_fiber_scheduler_create(monad_fiber_scheduler_t * this, size_t threads)
{
  this->threads = malloc(sizeof(pthread_t) * threads);
  this->thread_count = threads;
  MONAD_CCALL_ASSERT(pthread_mutex_init(&this->mutex, NULL));
  MONAD_CCALL_ASSERT(pthread_cond_init(&this->cond, NULL));

  this->thread_id_source = 1;
  monad_fiber_scheduler_task_queue_init(&this->task_queue);

  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

  for (size_t i = 0u; i < threads; i++)
  {
    MONAD_CCALL_ASSERT(pthread_create(this->threads + i, NULL, work, this));
  }


  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
}


void monad_fiber_scheduler_destroy (monad_fiber_scheduler_t * this)
{
  monad_fiber_scheduler_stop(this);

  for (size_t i = 0u; i < this->thread_count; i++)
    MONAD_CCALL_ASSERT(pthread_join(this->threads[i], NULL));

  free(this->threads);
  monad_fiber_scheduler_task_queue_destroy(&this->task_queue);

  MONAD_CCALL_ASSERT(pthread_cond_destroy(&this->cond));
  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
}

void monad_fiber_scheduler_post    (monad_fiber_scheduler_t * this, monad_fiber_scheduler_task_t * task, size_t priority)
{
  MONAD_ASSERT(task != 0);

  MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));

  monad_fiber_scheduler_task_queue_insert(&this->task_queue, task, priority);
  MONAD_CCALL_ASSERT(pthread_cond_signal(&this->cond));
  MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
}

void monad_fiber_scheduler_dispatch(monad_fiber_scheduler_t * this, monad_fiber_scheduler_task_t * task, size_t priority)
{
  if (this == monad_fiber_scheduler_current_)
    task->resume(task);
  else
    monad_fiber_scheduler_post(this, task, priority);
}

void monad_fiber_scheduler_stop    (monad_fiber_scheduler_t * this)
{
  this->thread_id_source = 0;
  MONAD_CCALL_ASSERT(pthread_cond_broadcast(&this->cond));
}

void monad_fiber_scheduler_work(monad_fiber_scheduler_t * this)
{
  monad_fiber_scheduler_current_ = this;
  if (this->thread_id_source != 0)
  {
    char name[16];
    snprintf(name, 16, "worker %u", ++(this->thread_id_source));
    MONAD_CCALL_ASSERT(pthread_setname_np(pthread_self(), name));
  }

  while (this->thread_id_source > 0)
  {
    MONAD_CCALL_ASSERT(pthread_mutex_lock(&this->mutex));
    while (this->task_queue.size == 0u)
    {
      if (this->thread_id_source != 0)
        pthread_cond_wait(&this->cond, &this->mutex);
      if (this->thread_id_source == 0)
      {
        while (this->task_queue.size > 0u)
        {
          monad_fiber_scheduler_task_t * t = monad_fiber_scheduler_task_queue_pop_front(&this->task_queue);
          t->destroy(t);
        }
        MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
        return;
      }
    }

    if (this->task_queue.size == 0u)
    {
      MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
      continue;
    }

    monad_fiber_scheduler_task_t * t = monad_fiber_scheduler_task_queue_pop_front(&this->task_queue);
    MONAD_CCALL_ASSERT(pthread_mutex_unlock(&this->mutex));
    t->resume(t);

  }
  monad_fiber_scheduler_current_ = NULL;
}