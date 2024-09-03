#include <stdio.h>
#include <sys/queue.h>
#include <threads.h>

#include <monad/core/tl_tid.h>

#define MONAD_FIBER_INTERNAL
#include "fiber_impl.h"

static SLIST_HEAD(, monad_thread_executor) g_thr_exec_head;
thread_local struct monad_thread_executor _tl_thr_exec;

void _monad_init_thread_executor(monad_thread_executor_t *thr_exec)
{
    thr_exec->thread = thrd_current();
    thr_exec->thread_id = get_tl_tid();

    monad_spinlock_init(&thr_exec->thread_ctx.lock);
    thr_exec->thread_ctx.type = MF_EXEC_HOST_THREAD;
    thr_exec->thread_ctx.thr_exec = thr_exec;

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
