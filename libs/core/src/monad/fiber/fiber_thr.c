#include <err.h>
#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/queue.h>
#include <threads.h>

#include <monad/core/spinlock.h>
#include <monad/core/thread.h>
#include <monad/fiber/fiber.h>

// This structure keeps track of a global list of all active
// monad_thread_executor objects that exist in the process; this is used for
// debugging
static struct thr_exec_global_state
{
    monad_spinlock_t lock;
    pthread_key_t key;
    SLIST_HEAD(, monad_thread_executor) head;
    size_t count;
} g_thr_execs;

thread_local struct monad_thread_executor _monad_tl_thr_exec;

static void monad_thread_executor_dtor(void *arg)
{
    monad_thread_executor_t *const thr_exec = arg;
    MONAD_SPINLOCK_LOCK(&g_thr_execs.lock);
    SLIST_REMOVE(&g_thr_execs.head, thr_exec, monad_thread_executor, next);
    --g_thr_execs.count;
    MONAD_SPINLOCK_UNLOCK(&g_thr_execs.lock);

    // XXX: add any final cleanup here
    (void)thr_exec;
}

void _monad_init_thread_executor(monad_thread_executor_t *thr_exec)
{
    int rc;
    pthread_attr_t thread_attrs;
    struct monad_exec_stack *thread_stack;
    size_t thread_stack_size;

    memset(thr_exec, 0, sizeof *thr_exec);
    atomic_init(&thr_exec->wakeup_queue, 0);
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

    MONAD_SPINLOCK_LOCK(&g_thr_execs.lock);
    SLIST_INSERT_HEAD(&g_thr_execs.head, thr_exec, next);
    ++g_thr_execs.count;
    rc = pthread_setspecific(g_thr_execs.key, thr_exec);
    if (rc != 0) {
        errno = rc;
        err(1, "pthread_setspecific(3) failed");
    }
    MONAD_SPINLOCK_UNLOCK(&g_thr_execs.lock);
}

void _monad_thread_executor_busy_wait(
    monad_thread_executor_t *thr_exec, monad_fiber_wait_queue_t *wq)
{
    uintptr_t expected_wakeup_queue;
    bool swapped;

    // Spin until the wakeup side writes the expected value
    do {
        expected_wakeup_queue = (uintptr_t)wq;
        swapped = atomic_compare_exchange_weak_explicit(
            &thr_exec->wakeup_queue,
            &expected_wakeup_queue,
            0,
            memory_order_acq_rel,
            memory_order_relaxed);
    }
    while (!swapped);

    thr_exec->thread_ctx.prev_wq = wq;
}

bool _monad_thread_executor_wakeup(
    monad_thread_executor_t *thr_exec, monad_fiber_wait_queue_t *wq)
{
    atomic_store_explicit(
        &thr_exec->wakeup_queue, (uintptr_t)wq, memory_order_release);
    return true;
}

static void __attribute((constructor)) init_thread_executor_list()
{
    int rc;

    monad_spinlock_init(&g_thr_execs.lock);
    rc = pthread_key_create(&g_thr_execs.key, monad_thread_executor_dtor);
    if (rc != 0) {
        errno = rc;
        err(1, "pthread_key_create(3) failed");
    }
    SLIST_INIT(&g_thr_execs.head);
}

static void __attribute__((destructor)) cleanup_thread_executor_list()
{
    while (!SLIST_EMPTY(&g_thr_execs.head)) {
        monad_thread_executor_dtor(SLIST_FIRST(&g_thr_execs.head));
    }
    (void)pthread_key_delete(g_thr_execs.key);
}
