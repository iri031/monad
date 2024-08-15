#include <errno.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/spinlock.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_util.h>

// Used to link all monad_fiber_t objects together, so information about
// them can be dumped when a crash occurs
static struct fiber_debug_info {
    atomic_bool initialized;
    monad_spinlock_t lock;
    TAILQ_HEAD(, monad_fiber) fibers;
} g_fiber_debug_info;

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