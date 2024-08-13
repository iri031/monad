#define _GNU_SOURCE // For pthread_getname_np(3)
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/bit_util.h>
#include <monad/core/dump.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_util.h>

// fiber_thr.c provides this special function to dump its internal state
extern void _monad_dump_thread_fiber_state(const void *arg,
                                           monad_dump_ctx_t *tfs_ctx);

enum monad_fiber_type {
    MONAD_FIBER_TYPE_USER,
    MONAD_FIBER_TYPE_THREAD,
    MONAD_FIBER_TYPE_THREAD_WAKEUP
};

static const char *FIBER_TYPE_NAMES[] = {
    [MONAD_FIBER_TYPE_USER] = "usr",
    [MONAD_FIBER_TYPE_THREAD] = "thr",
    [MONAD_FIBER_TYPE_THREAD_WAKEUP] = "thr_wake"
};

static const char *FIBER_STATE_NAMES[] = {
    [MONAD_FIBER_INIT] = "INIT",
    [MONAD_FIBER_CAN_RUN] = "CAN_RUN",
    [MONAD_FIBER_SLEEP] = "SLEEP",
    [MONAD_FIBER_RUN_QUEUE] = "RUN_QUEUE",
    [MONAD_FIBER_RUNNING] = "RUNNING",
    [MONAD_FIBER_TW_SUSPEND] = "THR_WAIT",
    [MONAD_FIBER_RETURN] = "RETURN"
};

// Used to link all monad_fiber_t objects together, so information about
// them can be dumped when a crash occurs
static struct fiber_debug_info {
    atomic_bool initialized;
    monad_spinlock_t lock;
    TAILQ_HEAD(, monad_fiber) fibers;
} g_fiber_debug_info;

static enum monad_fiber_type get_fiber_type(const monad_fiber_t *fiber) {
    if (monad_fiber_is_thread_fiber(fiber))
        return MONAD_FIBER_TYPE_THREAD;
    else if (fiber->ffunc == nullptr)
        return MONAD_FIBER_TYPE_THREAD_WAKEUP;
    else
        return MONAD_FIBER_TYPE_USER;
}

static void try_init_global_state() {
    bool is_initialized = false;
    if (!atomic_compare_exchange_strong(&g_fiber_debug_info.initialized,
                                        &is_initialized, true))
        return;
    monad_spinlock_init(&g_fiber_debug_info.lock);
    TAILQ_INIT(&g_fiber_debug_info.fibers);
}

int monad_fiber_alloc_stack(size_t *stack_size, monad_fiber_stack_t *stack) {
    const int page_size = getpagesize();
    if (stack_size == nullptr || stack == nullptr)
        return EFAULT;
    if ((ptrdiff_t)*stack_size - page_size < page_size)
        return EINVAL;
    stack->stack_base = mmap(nullptr, *stack_size, PROT_READ | PROT_WRITE,
                             MAP_ANONYMOUS | MAP_PRIVATE | MAP_STACK, -1, 0);
    if (stack->stack_base == MAP_FAILED)
        return errno;
    if (mprotect(stack->stack_base, page_size, PROT_NONE) == -1)
        return errno;
    *stack_size -= page_size;
    stack->stack_bottom = (uint8_t*)stack->stack_base + page_size;
    stack->stack_top = (uint8_t*)stack->stack_bottom + *stack_size;
    return 0;
}

void monad_fiber_free_stack(monad_fiber_stack_t stack)
{
    const size_t mapped_size =
        (size_t)((const uint8_t*)stack.stack_top -
                 (const uint8_t*)stack.stack_base);
    munmap(stack.stack_base, mapped_size);
}

void monad_fiber_dump(const monad_fiber_t *fiber, monad_dump_ctx_t *fiber_ctx) {
    constexpr size_t THR_NAME_MAX = 16; // From linux pthread_getname_np(3)
    char thr_name[THR_NAME_MAX];
    char ptr_buf[MONAD_DUMP_CHECK_PTR_SMALL_SIZE];
    monad_dump_ctx_t stack_ctx;
    monad_dump_ctx_t stats_ctx;

    fiber_ctx->max_field_length = sizeof "last_thread" - 1;
    if (pthread_getname_np(fiber->last_thread, thr_name, sizeof thr_name) != 0)
        strncpy(thr_name, "<unknown>", sizeof thr_name);

#define MDC_PTR(PTR) \
    monad_dump_check_and_deref_ptr((PTR), 0, ptr_buf, sizeof ptr_buf)

#define FIBER_WF(...) monad_dump_printf_field(fiber_ctx, __VA_ARGS__)
    FIBER_WF("name", "%s", fiber->name);
    FIBER_WF("address", "%s [%s]", MDC_PTR(fiber),
             FIBER_TYPE_NAMES[get_fiber_type(fiber)]);
    FIBER_WF("priority", "%ld", fiber->priority);
    FIBER_WF("state", "%s (%d)", FIBER_STATE_NAMES[fiber->state], fiber->state);
    FIBER_WF("wq/rq/tfs", "%s", MDC_PTR(fiber->wait_queue));
    FIBER_WF("suspended_ctx", MDC_PTR(fiber->suspended_ctx));
    FIBER_WF("prev_fiber", MDC_PTR(fiber->prev_fiber));
    FIBER_WF("last_thread", "%s (%d)", thr_name, fiber->last_thread_id);

    FIBER_WF("stack", nullptr);
    monad_dump_ctx_push(&stack_ctx, fiber_ctx);
    stack_ctx.max_field_length = sizeof "bottom" - 1;
#define STACK_WF(...) monad_dump_printf_field(&stack_ctx, __VA_ARGS__)
    STACK_WF("base", "%s", MDC_PTR(fiber->stack.stack_base));
    STACK_WF("bottom", "%s", MDC_PTR(fiber->stack.stack_bottom));
    STACK_WF("top", "%s", MDC_PTR(fiber->stack.stack_top));
    STACK_WF("used", "%zu KiB",
             bit_div_ceil(monad_fiber_get_used_stack_space(fiber->stack, fiber->suspended_ctx), 10));
    STACK_WF("free", "%zu KiB",
             bit_div_ceil(monad_fiber_get_free_stack_space(fiber->stack, fiber->suspended_ctx), 10));
#undef STACK_WF
    (void)monad_dump_ctx_pop(&stack_ctx);

    FIBER_WF("stats", nullptr);
    monad_dump_ctx_push(&stats_ctx, fiber_ctx);
    stats_ctx.max_field_length = sizeof "migrate" - 1;
#define STATS_WF(...) monad_dump_printf_field(&stats_ctx, __VA_ARGS__)
    STATS_WF("reset", "%zu", fiber->stats.total_reset);
    STATS_WF("run", "%zu", fiber->stats.total_run);
    STATS_WF("sleep", "%zu", fiber->stats.total_sleep);
    STATS_WF("migrate", "%zu", fiber->stats.total_migrate);
#undef STATS_WF
    (void)monad_dump_ctx_pop(&stats_ctx);

#undef FIBER_WF
}

void monad_fiber_debug_add(monad_fiber_t *fiber) {
    try_init_global_state();
    MONAD_DEBUG_ASSERT(fiber != nullptr);
    MONAD_SPINLOCK_LOCK(&g_fiber_debug_info.lock);
    TAILQ_INSERT_TAIL(&g_fiber_debug_info.fibers, fiber, fibers_link);
    monad_spinlock_unlock(&g_fiber_debug_info.lock);
}

void monad_fiber_debug_remove(monad_fiber_t *fiber) {
    MONAD_DEBUG_ASSERT(fiber != nullptr &&
                       atomic_load(&g_fiber_debug_info.initialized) == true);
    MONAD_SPINLOCK_LOCK(&g_fiber_debug_info.lock);
    TAILQ_REMOVE(&g_fiber_debug_info.fibers, fiber, fibers_link);
    monad_spinlock_unlock(&g_fiber_debug_info.lock);
}

void monad_fiber_debug_dump_all(monad_dump_ctx_t *all_fibers_ctx) {
    monad_dump_ctx_t fiber_ctx;
    monad_fiber_t *fiber;
    unsigned count = 0;

    monad_dump_println(all_fibers_ctx, "global fiber state dump");
    if (!MONAD_SPINLOCK_TRY_LOCK(&g_fiber_debug_info.lock)) {
        sleep(1);
        if (!MONAD_SPINLOCK_TRY_LOCK(&g_fiber_debug_info.lock)) {
            monad_dump_println(all_fibers_ctx,
                               "error: cannot lock g_fiber_debug_info lock");
            return;
        }
    }
    TAILQ_FOREACH(fiber, &g_fiber_debug_info.fibers, fibers_link) {
        monad_dump_println(all_fibers_ctx, "* FIBER %u: %p [%s]", count++,
                           fiber, FIBER_TYPE_NAMES[get_fiber_type(fiber)]);
        monad_dump_ctx_push(&fiber_ctx, all_fibers_ctx);
        switch (get_fiber_type(fiber)) {
        case MONAD_FIBER_TYPE_USER:
            monad_fiber_dump(fiber, &fiber_ctx);
            break;
        case MONAD_FIBER_TYPE_THREAD:
            _monad_dump_thread_fiber_state(fiber->thread_fs, &fiber_ctx);
            break;
        case MONAD_FIBER_TYPE_THREAD_WAKEUP:
            monad_dump_println(&fiber_ctx,
                               "<handled by TFS state dump function>");
            break;
        }
        (void)monad_dump_ctx_pop(&fiber_ctx);
    }
    monad_spinlock_unlock(&g_fiber_debug_info.lock);
}

void monad_fiber_debug_sigaction(int /*unused*/, siginfo_t *siginfo,
                                 void *ucontext) {
    monad_dump_backend_t dump_be;
    monad_dump_ctx_t siginfo_ctx;
    monad_dump_ctx_t *const root_ctx =
        monad_dump_backend_init_fd(&dump_be, 2, STDERR_FILENO);

    monad_dump_println(root_ctx, "received signal %d", siginfo->si_signo);
    monad_dump_ctx_push(&siginfo_ctx, root_ctx);
    monad_dump_siginfo(&siginfo_ctx, siginfo, ucontext);
    monad_dump_ctx_pop(&siginfo_ctx);

    monad_dump_println(root_ctx, "stack trace:");
    monad_dump_stacktrace(root_ctx);

    monad_fiber_debug_dump_all(root_ctx);
}