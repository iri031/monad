/**
 * @file
 *
 * This file contains the code for the "thread fiber" feature.
 *
 * Most fibers are user-created, but in the current db implementation, an
 * ordinary thread of execution is sometimes treated as though it is running
 * on a fiber. This is an API idiom that Boost.Fiber allowed, thus the
 * existing db code grew to rely on it.
 *
 * For this to work, we need to make an ordinary thread context pretend that it
 * is a fiber. This is called a "thread fiber" in the code. To simplify fiber.c,
 * most of the code for thread fiber support lives in this file, fiber_thr.c
 *
 * There are two parts of thread fiber support:
 *
 *   1. Creating a "fake" `monad_fiber_t` that represents a thread context;
 *      this is what is returned if you call `monad_fiber_self()` in the cotext
 *      of a normal thread instead of a "real" fiber
 *
 *   2. Creating a dummy "wakeup fiber" that the thread fiber switches to, when
 *      it goes to sleep on a wait channel. For performance reasons, the wakeup
 *      fiber spins until it is woken up
 */

#define _GNU_SOURCE // For pthread_getattr_np(3)
#include <errno.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#if MONAD_HAVE_ASAN
#include <sanitizer/asan_interface.h>
#endif

#include <monad/core/assert.h>
#include <monad/core/tl_tid.h>
#include <monad/fiber/fiber.h>
#include "fiber_ctx.h"

// The wakeup fiber runs almost no code, thus requires only a few stack pages
constexpr size_t WAKEUP_STACK_PAGES = 4;

struct thread_fiber_state {
    monad_fiber_t thread_fiber;  ///< Fiber representing a normal thread context
    monad_fiber_t wakeup_fiber;  ///< Shim "wakeup" fiber; used when sleeping
    atomic_uintptr_t wakeup_q;   ///< Address of wait_queue; spin until written
};

static thread_local struct thread_fiber_state tl_state;

extern monad_fiber_t *_monad_fiber_resume(monad_fiber_t *cur_fiber,
                                          monad_fiber_transfer_t xfer_from);

extern void _monad_fiber_switch(monad_fiber_t *cur_fiber,
                                monad_fiber_t *next_fiber);

static void free_wakeup_stack(monad_fiber_stack_t *wakeup_stack) {
    const size_t mapped_size = (size_t)((const uint8_t*)wakeup_stack->stack_top - (const uint8_t*)wakeup_stack->stack_base);
    munmap(wakeup_stack->stack_base, mapped_size);
}

[[noreturn]] static void wakeup_entrypoint(monad_fiber_transfer_t xfer_from) {
    // Entry point of the wakeup fiber. This pretends to be the jump origin of
    // the thread fiber. It waits for the wait queue to signal that it's time
    // to wake up the thread fiber, then initiates the context jump back to the
    // thread fiber.
    bool swapped;
    monad_fiber_t *thread_fiber;
    struct thread_fiber_state *tfs;
    monad_fiber_t *const wakeup_fiber =
        _monad_fiber_resume(monad_fiber_self(), xfer_from);

    thread_fiber = wakeup_fiber->prev_fiber;
    tfs = thread_fiber->thread_fiber_state;

    MONAD_DEBUG_ASSERT(monad_fiber_is_thread_fiber(thread_fiber));
    MONAD_DEBUG_ASSERT(wakeup_fiber == &tfs->wakeup_fiber);

    do {
        // The only thing the scheduling fiber does is busy-wait for the
        // wait channel to wake up the thread fiber
        tfs->wakeup_fiber.status.state = MONAD_FIBER_SPIN_WAIT;
        tfs->wakeup_fiber.status.eval = 0;

        // Spin until a worker thread fills this in
        while (atomic_load_explicit(&tfs->wakeup_q, memory_order_acquire) == 0);
        uintptr_t expected_wait_queue = (uintptr_t)tfs->thread_fiber.wait_queue;
        swapped = atomic_compare_exchange_strong(&tfs->wakeup_q, &expected_wait_queue, 0);
        MONAD_ASSERT(swapped);
        // Reset wakeup_q for next time and switch back to the thread fiber
        tfs->wakeup_q = 0;
        tfs->wakeup_fiber.status.state = MONAD_FIBER_SLEEP; // XXX: not really
        _monad_fiber_switch(&tfs->wakeup_fiber, thread_fiber);
    } while (true);
}

static void init_thread_fiber_state(struct thread_fiber_state *tfs) {
    // The way we support thread fibers is by creating a "wakeup" fiber, which
    // pretends to be the context that originally jumped into the thread fiber,
    // thus it is the place where we return to upon suspension.
    //
    // In reality, the thread fiber's context was created directly by the
    // operating system; unlike a "real" fiber, we did not jump into the thread
    // using the `monad_fiber_run` function. Pretending that we did, however,
    // makes the suspension logic in fiber.c work the same way.
    int rc;
    pthread_attr_t thread_attrs;
    monad_fiber_stack_t wakeup_stack;
    size_t wakeup_stack_size;
    size_t thread_stack_size;
    const size_t page_size = getpagesize();

    memset(tfs, 0, sizeof *tfs);

    // The `+ page_size` factor in the mmap size is so that we map one
    // additional page at the bottom of the stack, for the guard page
    wakeup_stack_size = WAKEUP_STACK_PAGES * page_size;
    wakeup_stack.stack_base = mmap(nullptr, wakeup_stack_size + page_size,
                                   PROT_READ | PROT_WRITE,
                                   MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (wakeup_stack.stack_base == MAP_FAILED) {
        fprintf(stderr, "mmap(2) of wakeup stack failed: %d\n", errno);
        abort();
    }
    if (mprotect(wakeup_stack.stack_base, page_size, PROT_NONE) == -1) {
        fprintf(stderr, "mprotect(2) of wakeup guard page failed: %d\n",
                errno);
        abort();
    }
    wakeup_stack.stack_bottom = (uint8_t*)wakeup_stack.stack_base + page_size;
    wakeup_stack.stack_top = (uint8_t*)wakeup_stack.stack_bottom + wakeup_stack_size;
    monad_fiber_init(&tfs->wakeup_fiber, wakeup_stack);
#if 0
    pthread_cleanup_push((void(*)(void *))free_wakeup_stack,
                         &tfs->wakeup_fiber.stack);
#endif
    tfs->wakeup_fiber.priority = MONAD_FIBER_PRIO_LOWEST;
    tfs->wakeup_fiber.fctx =
        make_fcontext(wakeup_stack.stack_top, wakeup_stack_size,
                      wakeup_entrypoint);

    tfs->thread_fiber.priority = MONAD_FIBER_PRIO_LOWEST;
    tfs->thread_fiber.status.state = MONAD_FIBER_RUN;
    tfs->thread_fiber.thread_fiber_state = tfs;
    tfs->thread_fiber.last_thread_id = get_tl_tid();

    // This is what makes the machinery work: even though the thread fiber is
    // not a real fiber, we pretend that control was transferred to it from the
    // wakeup fiber. When the thread fiber is put to sleep on a wait queue, it
    // will switch "back" into the wakeup fiber
    tfs->thread_fiber.prev_fiber = &tfs->wakeup_fiber;

    // Get the thread's stack area
    // TODO(ken): this is very Linux-specific

    rc = pthread_getattr_np(pthread_self(), &thread_attrs);
    if (rc != 0) {
        fprintf(stderr, "fatal: pthread_getattr_np(3): %d\n", rc);
        abort();
    }
    rc = pthread_attr_getstack(&thread_attrs,
                               &tfs->thread_fiber.stack.stack_bottom,
                               &thread_stack_size);
    if (rc != 0) {
        fprintf(stderr, "fatal: pthread_attr_getstack(3): %d\n", rc);
        abort();
    }
    tfs->thread_fiber.stack.stack_base = tfs->thread_fiber.stack.stack_bottom;
    tfs->thread_fiber.stack.stack_top =
        (uint8_t*)tfs->thread_fiber.stack.stack_bottom + thread_stack_size;
}

extern monad_fiber_t *_monad_get_thread_fiber() {
    if (tl_state.thread_fiber.status.state == MONAD_FIBER_INIT)
        init_thread_fiber_state(&tl_state);
    return &tl_state.thread_fiber;
}

extern void _monad_wakeup_thread_fiber(struct thread_fiber_state *tfs,
                                       monad_fiber_wait_queue_t *wq) {
    atomic_store_explicit(&tfs->wakeup_q, (uintptr_t)wq, memory_order_release);
}
