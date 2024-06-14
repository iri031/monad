#pragma once


#if defined(__cplusplus)
extern "C"
{
#endif

#include "current.h"

#include <stdbool.h>
#include <stddef.h>

#include <pthread.h>

typedef struct monad_fiber_channel
{
    size_t capacity, size, offset, element_size;
    void *data;
    pthread_mutex_t mutex;

    struct monad_fiber_channel_read_op *pending_reads;
    struct monad_fiber_channel_write_op *pending_writes;

} monad_fiber_channel_t;

// element_size == 0 means there's no buffer, i.e. it's void.
void monad_fiber_channel_create(
    monad_fiber_channel_t *, size_t capacity, size_t element_size);
void monad_fiber_channel_destroy(monad_fiber_channel_t *);

void monad_fiber_channel_close(monad_fiber_channel_t *);

bool monad_fiber_channel_try_read(monad_fiber_channel_t *, void *target);
bool monad_fiber_channel_try_write(monad_fiber_channel_t *, void const *source);

int monad_fiber_channel_read(monad_fiber_channel_t *, void *target);
int monad_fiber_channel_write(monad_fiber_channel_t *, void const *source);

int monad_fiber_channel_send(monad_fiber_channel_t *, void const * source);



#if defined(__cplusplus)
}
#endif
