/**
 * @file
 *
 * This file contains the code for the "thread fiber" feature. See the
 * section on thread fibers in fiber.md for an explanation of these.
 */

#define _GNU_SOURCE // For pthread_getattr_np(3)
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/core/tl_tid.h>
#include <monad/fiber/fiber.h>

// The wakeup fiber runs almost no code, thus requires only a few stack pages
static size_t const WAKEUP_STACK_PAGES = 8;

struct thread_fiber_stats
{
    size_t immediate_wakeup; ///< # of times wakeup was ready immediately
};

struct thread_fiber_state
{
    monad_fiber_t thread_fiber; ///< Fiber representing a normal thread context
    monad_fiber_t wakeup_fiber; ///< Shim "wakeup" fiber; used when sleeping
    atomic_uintptr_t wakeup_q; ///< Address of wait_queue; spin until non-zero
    struct thread_fiber_stats stats; ///< Thread-fiber-specific statistics
};

static thread_local struct thread_fiber_state tl_state;

extern monad_fiber_suspend_info_t
_monad_fiber_finish_switch(monad_context_task task);

extern void _monad_fiber_suspend(
    monad_fiber_t *cur_fiber, enum monad_fiber_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval);

[[noreturn]] static monad_c_result wakeup_entrypoint(monad_context_task task)
{
    // Entry point of the wakeup fiber. This pretends to be the jump origin of
    // the thread fiber. It waits for a synchronization primitive (e.g., a
    // channel or semaphore) to signal that it's time to wake up the thread
    // fiber, then initiates the context switch back to the thread fiber
    bool swapped;
    monad_fiber_t *thread_fiber;
    monad_fiber_t *wakeup_fiber;
    struct thread_fiber_state *tfs;
    uintptr_t wakeup_q;
    uintptr_t expected_wait_queue;

    // Finish the first switch that brought us here
    (void)_monad_fiber_finish_switch(task);
    wakeup_fiber = monad_fiber_self();
    thread_fiber = wakeup_fiber->prev_fiber;
    tfs = thread_fiber->thread_fs;

    MONAD_DEBUG_ASSERT(monad_fiber_is_thread_fiber(thread_fiber));
    MONAD_DEBUG_ASSERT(wakeup_fiber == &tfs->wakeup_fiber);

    do {
        // The only thing this wakeup fiber does is busy-wait for a
        // synchronization primitive to wake us up, via a call to
        // _monad_wakeup_thread_fiber

        // Spin until someone wakes us
        wakeup_q = atomic_load_explicit(&tfs->wakeup_q, memory_order_acquire);
        if (wakeup_q != 0) {
            ++tfs->stats.immediate_wakeup;
        }
        else {
            while (atomic_load_explicit(&tfs->wakeup_q, memory_order_acquire) ==
                   0)
                ;
        }

        expected_wait_queue = (uintptr_t)thread_fiber->wait_queue;
        if (expected_wait_queue == 0) {
            expected_wait_queue = (uintptr_t)thread_fiber->prev_wq;
        }
        swapped = atomic_compare_exchange_strong(
            &tfs->wakeup_q, &expected_wait_queue, 0);
        MONAD_ASSERT(swapped);

        // This wakeup means the thread fiber's resource is ready; suspend
        // ourselves and switch back into it
        MONAD_SPINLOCK_LOCK(&wakeup_fiber->lock);
        _monad_fiber_suspend(
            wakeup_fiber, MF_STATE_EXEC_WAIT, MF_SUSPEND_SLEEP, 0);
    }
    while (true);
}

static monad_context_switcher get_thread_local_context_switcher()
{
    // I'd personally put this function into C++ so thread locals get
    // destructed properly
    static thread_local monad_context_switcher switcher;
    if (switcher == nullptr) {
        MONAD_CONTEXT_CHECK_RESULT(
            MONAD_FIBER_CONTEXT_SWITCHER.create(&switcher));
    }
    return switcher;
}

static void init_wakeup_fiber(monad_fiber_t *wakeup_fiber)
{
    char namebuf[MONAD_FIBER_NAME_LEN + 1];
    struct monad_fiber_attr_t attr = {
        {.stack_size = WAKEUP_STACK_PAGES * getpagesize()}};

    monad_fiber_init(wakeup_fiber, get_thread_local_context_switcher(), &attr);
    wakeup_fiber->priority = MONAD_FIBER_PRIO_LOWEST;
    wakeup_fiber->state = MF_STATE_EXEC_WAIT;
    wakeup_fiber->head.user_code = wakeup_entrypoint;
    wakeup_fiber->last_thread = pthread_self();
    wakeup_fiber->last_thread_id = get_tl_tid();
    snprintf(namebuf, sizeof namebuf, "WUF_%d", wakeup_fiber->last_thread_id);
    (void)monad_fiber_set_name(wakeup_fiber, namebuf);
}

static void init_thread_fiber(monad_fiber_t *thread_fiber)
{
    char namebuf[MONAD_FIBER_NAME_LEN + 1];

    monad_fiber_init(thread_fiber, nullptr, nullptr);
    thread_fiber->priority = MONAD_FIBER_PRIO_LOWEST;
    thread_fiber->state = MF_STATE_RUNNING;
    thread_fiber->last_thread = pthread_self();
    thread_fiber->last_thread_id = get_tl_tid();
    snprintf(namebuf, sizeof namebuf, "THR_%d", thread_fiber->last_thread_id);
    (void)monad_fiber_set_name(thread_fiber, namebuf);
}

static void init_thread_fiber_state(struct thread_fiber_state *tfs)
{
    // The way we support thread fibers is by creating a "wakeup" fiber, which
    // pretends to be the context that originally jumped into the thread fiber,
    // thus it is the place where we return to upon suspension.
    //
    // In reality, the thread fiber's context was created directly by the
    // operating system; unlike a "real" fiber, we did not originally jump into
    // the thread using the `monad_fiber_run` function. Pretending that we did,
    // however, makes the suspension logic in fiber.c work the same way.
    memset(tfs, 0, sizeof *tfs);
    init_wakeup_fiber(&tfs->wakeup_fiber);
    init_thread_fiber(&tfs->thread_fiber);

    tfs->thread_fiber.thread_fs = tfs;
    // Pretend control was transferred to the thread fiber from the wakeup
    // fiber. When the thread fiber is put to sleep on a wait queue, it will
    // switch "back" into the wakeup fiber
    tfs->thread_fiber.prev_fiber = &tfs->wakeup_fiber;
}

extern monad_fiber_t *_monad_get_thread_fiber()
{
    if (MONAD_UNLIKELY(tl_state.thread_fiber.state == MF_STATE_INIT)) {
        init_thread_fiber_state(&tl_state);
    }
    return &tl_state.thread_fiber;
}

extern void _monad_wakeup_thread_fiber(
    struct thread_fiber_state *tfs, monad_fiber_wait_queue_t *wq)
{
    atomic_store_explicit(&tfs->wakeup_q, (uintptr_t)wq, memory_order_release);
}
