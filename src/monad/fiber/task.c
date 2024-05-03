#include <malloc.h>
#include <monad/fiber/assert.h>
#include <monad/fiber/task.h>
#include <string.h>

static size_t const monad_fiber_task_queue_chunk = 256;

void monad_fiber_task_queue_init(struct monad_fiber_task_queue *this)
{
    this->memory = malloc(
        sizeof(struct monad_fiber_task_node) * monad_fiber_task_queue_chunk);
    this->capacity = monad_fiber_task_queue_chunk;
    this->data = this->memory;
    this->size = 0u;
}

void monad_fiber_task_queue_destroy(struct monad_fiber_task_queue *this)
{
    free(this->memory);
}

void monad_fiber_task_queue_grow(struct monad_fiber_task_queue *this)
{
    struct monad_fiber_task_node *pre = this->data;
    this->capacity += monad_fiber_task_queue_chunk;
    void *new_mem = realloc(
        this->memory, this->capacity * sizeof(struct monad_fiber_task_node));

    MONAD_ASSERT(new_mem != NULL);
    this->memory = new_mem;

    if (this->memory != this->data) {
        this->data = this->memory + (this->data - pre);
    }
}

struct monad_fiber_task_node
monad_fiber_task_queue_pop_front(struct monad_fiber_task_queue *this)
{
    MONAD_ASSERT(this->size > 0ull);
    struct monad_fiber_task_node *t = this->data;
    MONAD_ASSERT(t != NULL);

    this->data++;
    this->size--;
    if (this->data == (this->memory + this->capacity)) {
        this->data = this->memory;
    }

    return *t;
}

void monad_fiber_task_queue_insert(
    struct monad_fiber_task_queue *this, monad_fiber_task_t *task,
    int64_t priority)
{
    if (this->size == this->capacity) { // resize
        monad_fiber_task_queue_grow(this);
    }

    struct monad_fiber_task_node *itr = this->data,
                                 *end = this->data + this->size;

    if (this->size == 0u)
    {
        this->size++;
        itr = this->data = this->memory;
        itr->task = task;
        itr->priority = priority;
        return;
    }

  // push back & push front
  if (this->data->priority > priority) // we can push front
  {
    if (this->data == this->memory)
      this->data = this->memory + this->capacity;

    itr = --this->data;
    itr->priority = priority;
    itr->task = task;
    this->size++;
    return ;
  }

    if (end >= (this->memory + this->capacity)) {
        end -= this->capacity;
    }

    MONAD_ASSERT(end >= this->memory);

    while (itr != end) {
        if (itr->priority > priority) {
            break;
        }

        itr++;
        if (itr == (this->memory + this->capacity)) {
            itr = this->memory;
        }
    }

    MONAD_ASSERT(itr <= (this->memory + this->capacity));

    if (itr != end) // we need to shift elements right
    {
        if (end < itr) // are we wrapping around the end of the buffer
        {
            struct monad_fiber_task_node *mem_end =
                this->memory + this->capacity;

            // this shifts the lower part (DEF in the below example)
            memmove(
                this->memory + 1,
                this->memory,
                (size_t)(end - this->memory) *
                    sizeof(struct monad_fiber_task_node));
            if (itr == mem_end) // we're at the end of memory, no need to do a
                                // second shift.
            {
                // that's the insert
                // | D | E | F |   |  | A | B | C |
                // | X | D | E | F |  | A | B | C |
                itr = this->memory;
            }
            else {

                // | D | E | F |   |   | A | B | C |
                // | C | D | E | F |   | A | X | B |
                this->memory[0] =
                    this->memory[this->capacity - 1]; // wrap one element around
                                                      // (C)
                // move B
                // | C | D | E | F |   | A | X | B |
                //                           ^ itr   ^ mem_end
                memmove(
                    itr + 1,
                    itr,
                    (size_t)((mem_end - itr) - 1) *
                        sizeof(struct monad_fiber_task_node));
            }
        }
        else {
            memmove(
                itr + 1,
                itr,
                (size_t)(end - itr) * sizeof(struct monad_fiber_task_node));
        }
    }
    itr->task = task;
    itr->priority = priority;
    this->size++;
}
