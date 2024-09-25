#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

/**
 * @file
 *
 * This file contains a few thread routines which are not standardized
 * in pthread(3) at this time.
 */

#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>

#include <monad/core/likely.h>

typedef long monad_tid_t;
extern __thread monad_tid_t _monad_tl_tid;
void _monad_tl_tid_init();

/// Get the system ID of the calling thread
static inline monad_tid_t monad_thread_get_id()
{
    if (MONAD_UNLIKELY(!_monad_tl_tid)) {
        _monad_tl_tid_init();
    }
    return _monad_tl_tid;
}

/// Set the name of the calling thread
int monad_thread_set_name(char const *name);

/// Get the base address and size of a thread's stack
int monad_thread_get_stack(pthread_t thread, void **stack_addr, size_t *stack_size);

#ifdef __cplusplus
}
#endif
