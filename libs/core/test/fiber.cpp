#include <bit>
#include <cstddef>
#include <cstdint>

#include <gtest/gtest.h>

#include <monad/fiber/fiber.h>

static std::uintptr_t yield_forever(std::uintptr_t arg0) noexcept
{
    auto *const pdone = std::bit_cast<std::atomic<bool> *>(arg0);
    std::uintptr_t y = 0;
    while (!pdone->load(std::memory_order::relaxed)) {
        monad_fiber_yield(y++);
    }
    return y;
}

TEST(fiber, basic)
{
    monad_fiber_t *fiber;
    monad_fiber_suspend_info_t suspend_info;
    std::atomic<bool> done;

    ASSERT_EQ(0, monad_fiber_create(nullptr, &fiber));

    // Nothing to run if we've never set a function
    ASSERT_EQ(ENXIO, monad_fiber_run(fiber, nullptr));

    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            std::bit_cast<std::uintptr_t>(&done)));

    done.store(false);
    for (std::uintptr_t expected = 0; expected < 10; ++expected) {
        ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
        ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
        ASSERT_EQ(expected, suspend_info.eval);
    }

    done.store(true);
    ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    ASSERT_EQ(10U, suspend_info.eval);
    ASSERT_EQ(ENXIO, monad_fiber_run(fiber, &suspend_info));

    // Reset the function; this resets the stack pointer to the beginning,
    // destroying the stack frame and thus the local state of the function;
    // the yield sequence will reset at 0.
    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            std::bit_cast<std::uintptr_t>(&done)));

    done.store(false);
    for (std::uintptr_t expected = 0; expected < 10; ++expected) {
        ASSERT_EQ(0, monad_fiber_run(fiber, &suspend_info));
        ASSERT_EQ(MF_SUSPEND_YIELD, suspend_info.suspend_type);
        ASSERT_EQ(expected, suspend_info.eval);
    }

    // The function may be reset at any time, not just before it has run or
    // after it has returned; be aware of this power though: C++ destructors
    // for objects living on stack frames which are abandoned will not be run!
    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            std::bit_cast<std::uintptr_t>(&done)));

    monad_fiber_destroy(fiber);
}
