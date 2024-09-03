#include <cstddef>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <monad/fiber/fiber.h>
#include <monad/fiber/future.hpp>
#include <monad/fiber/run_queue.h>

struct TestValue
{
    std::string s;
    std::vector<long> v;
};

namespace
{
    std::uintptr_t future_fiber_fn(std::uintptr_t arg0)
    {
        auto *const promise =
            std::bit_cast<monad::fiber::simple_promise<TestValue> *>(arg0);
        TestValue value = promise->get_future().get();
        return value.s.size() + value.v.size();
    }
}

TEST(future, serial_basic)
{
    monad_fiber_t *future_fiber;
    monad_run_queue *run_queue;
    monad_fiber_suspend_info_t suspend_info;
    monad::fiber::simple_promise<TestValue> promise;

    ASSERT_EQ(0, monad_fiber_create(nullptr, &future_fiber));
    ASSERT_EQ(
        0,
        monad_fiber_set_function(
            future_fiber,
            MONAD_FIBER_PRIO_HIGHEST,
            future_fiber_fn,
            std::bit_cast<std::uintptr_t>(&promise)));
    ASSERT_EQ(0, monad_run_queue_create(nullptr, 1, &run_queue));

    // Put the fiber into a run queue, so that it becomes associated with it.
    // This is what causes subsequent wake-ups to reschedule it there
    ASSERT_EQ(0, monad_run_queue_try_push(run_queue, future_fiber));
    ASSERT_EQ(future_fiber, monad_run_queue_try_pop(run_queue));

    // Run the fiber until it goes to sleep waiting for the promise to publish
    ASSERT_EQ(0, monad_fiber_run(future_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_SLEEP, suspend_info.suspend_type);

    // Because the condition to wake up the fiber has not occurred, the
    // run queue remains empty
    ASSERT_EQ(nullptr, monad_run_queue_try_pop(run_queue));

    TestValue value = {.s = "Hello, World!", .v = {1, 2, 3, 4, 5}};
    std::size_t const expected_value = value.s.size() + value.v.size();

    // Set the value, which should cause the sleeping fiber to become
    // runnable immediately
    promise.set_value(value);
    ASSERT_EQ(future_fiber, monad_run_queue_try_pop(run_queue));

    // Run the fiber, which will wake up, read the message, and return
    // the expected value to us.
    ASSERT_EQ(0, monad_fiber_run(future_fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    ASSERT_EQ(expected_value, suspend_info.eval);

    monad_run_queue_destroy(run_queue);
    monad_fiber_destroy(future_fiber);
}
