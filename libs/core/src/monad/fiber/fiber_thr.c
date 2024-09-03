#include <err.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/queue.h>
#include <threads.h>

#include <monad/core/thread.h>

#define MONAD_FIBER_INTERNAL
#include "fiber_impl.h"

static SLIST_HEAD(, monad_thread_executor) g_thr_exec_head;
thread_local struct monad_thread_executor _tl_thr_exec;

void _monad_init_thread_executor(monad_thread_executor_t *thr_exec)
{
    int rc;
    pthread_attr_t thread_attrs;
    struct monad_exec_stack *thread_stack;
    size_t thread_stack_size;

    memset(thr_exec, 0, sizeof *thr_exec);
    thr_exec->thread = thrd_current();
    thr_exec->thread_id = monad_thread_get_id();

    thr_exec->thread_ctx.type = MF_EXEC_HOST_THREAD;
    thr_exec->thread_ctx.thr_exec = thr_exec;
    thr_exec->thread_ctx.stats = &thr_exec->stats;

    // Get the thread's stack area
    // TODO(ken): this is Linux-specific, and it's also potentially wrong if
    //  mapped with MAP_GROWSDOWN (its size could increase, and we won't know)
    thread_stack = &thr_exec->thread_ctx.stack;
    rc = pthread_getattr_np(pthread_self(), &thread_attrs);
    if (rc != 0) {
        fprintf(stderr, "fatal: pthread_getattr_np(3): %d\n", rc);
        abort();
    }
    rc = pthread_attr_getstack(
        &thread_attrs, &thread_stack->stack_bottom, &thread_stack_size);
    if (rc != 0) {
        fprintf(stderr, "fatal: pthread_attr_getstack(3): %d\n", rc);
        abort();
    }
    rc = pthread_attr_destroy(&thread_attrs);
    if (rc != 0) {
        fprintf(stderr, "fatal: pthread_attr_destroy(3): %d\n", rc);
        abort();
    }
    thread_stack->stack_base = thread_stack->stack_bottom;
    thread_stack->stack_top =
        (uint8_t *)thread_stack->stack_bottom + thread_stack_size;

    SLIST_INSERT_HEAD(&g_thr_exec_head, thr_exec, next);
}

static void cleanup_thread_executor(monad_thread_executor_t *thr_exec)
{
    (void)thr_exec;
}

static void __attribute((constructor)) init_thread_executor_list()
{
    SLIST_INIT(&g_thr_exec_head);
}

static void __attribute__((destructor)) cleanup_thread_executor_list()
{
    monad_thread_executor_t *thr_exec;
    SLIST_FOREACH(thr_exec, &g_thr_exec_head, next)
    {
        cleanup_thread_executor(thr_exec);
    }
}
