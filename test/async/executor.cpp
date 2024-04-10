#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/executor.h"

#include "monad/async/task.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <utility>

/* Post runtime pluggable context switchers:

   Task attach to task initiate took 360 ticks.
   Task initiate to task detach took 360 ticks.
   Task executed for a total of 360 ticks.

   Task attach to task initiate took 468 ticks.
   Task initiate to task suspend await took 432 ticks.
   Task suspend await to task suspend completed took 17352 ticks.
   Task suspend completed to task resume took 180 ticks.
   Task resume to task detach took 432 ticks.
   Task executed for a total of 864 ticks.


   Initiated, executed and tore down 2.52525e+07 ops/sec which is 39.6002 ns/op.


   Suspend-resume 1.16596e+07 ops/sec which is 85.7663 ns/op.
*/

TEST(async_result, works)
{
    auto r = monad_async_make_success(EINVAL);
    CHECK_RESULT(r);
    try {
        r = monad_async_make_failure(EINVAL);
        CHECK_RESULT(r);
    }
    catch (std::exception const &e) {
        EXPECT_STREQ(e.what(), "Invalid argument");
    }
}

TEST(executor, works)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    auto ex = make_executor(ex_attr);

    struct timespec ts
    {
        0, 0
    };

    auto r = monad_async_executor_run(ex.get(), 1, &ts);
    try {
        CHECK_RESULT(r);
    }
    catch (std::exception const &e) {
        EXPECT_STREQ(e.what(), "Timer expired");
    }
    {
        auto begin = std::chrono::steady_clock::now();
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(1)) {
        }
    }
    monad_async_task_attr t_attr{};
    for (size_t n = 0; n < 10; n++) {
        auto s1 = make_context_switcher(monad_async_context_switcher_none);
        auto t1 = make_task(s1.get(), t_attr);
        bool did_run = false;
        t1->user_ptr = (void *)&did_run;
        t1->user_code = +[](monad_async_task task) -> monad_async_result {
            *(bool *)task->user_ptr = true;
            EXPECT_EQ(task->current_executor->current_task, task);
            EXPECT_EQ(task->current_executor->tasks_pending_launch, 0);
            EXPECT_EQ(task->current_executor->tasks_running, 1);
            EXPECT_EQ(task->current_executor->tasks_suspended, 0);
            return monad_async_make_success(5);
        };
        r = monad_async_task_attach(ex.get(), t1.get(), nullptr);
        CHECK_RESULT(r);
        EXPECT_TRUE(t1->is_pending_launch);
        EXPECT_FALSE(t1->is_running);
        EXPECT_FALSE(t1->is_suspended_awaiting);
        EXPECT_FALSE(t1->is_suspended_completed);
        EXPECT_EQ(ex->current_task, nullptr);
        EXPECT_EQ(ex->tasks_pending_launch, 1);
        EXPECT_EQ(ex->tasks_running, 0);
        EXPECT_EQ(ex->tasks_suspended, 0);
        r = monad_async_executor_run(ex.get(), 1, &ts);
        EXPECT_EQ(ex->tasks_pending_launch, 0);
        EXPECT_EQ(ex->tasks_running, 0);
        EXPECT_EQ(ex->tasks_suspended, 0);
        CHECK_RESULT(r);
        EXPECT_EQ(r.value, 1);
        EXPECT_FALSE(t1->is_pending_launch);
        EXPECT_FALSE(t1->is_running);
        EXPECT_FALSE(t1->is_suspended_awaiting);
        EXPECT_FALSE(t1->is_suspended_completed);
        CHECK_RESULT(t1->result);
        EXPECT_EQ(t1->result.value, 5);
        EXPECT_TRUE(did_run);
        if (n == 9) {
            std::cout << "   Task attach to task initiate took "
                      << (t1->ticks_when_resumed - t1->ticks_when_attached)
                      << " ticks.";
            std::cout << "\n   Task initiate to task detach took "
                      << (t1->ticks_when_detached - t1->ticks_when_resumed)
                      << " ticks.";
            std::cout << "\n   Task executed for a total of "
                      << t1->total_ticks_executed << " ticks." << std::endl;
        }
    }
    {
        static size_t n;
        for (n = 0; n < 10; n++) {
            auto s1 = make_context_switcher(monad_async_context_switcher_sjlj);
            auto t1 = make_task(s1.get(), t_attr);
            int did_run = 0;
            t1->user_ptr = (void *)&did_run;
            t1->user_code = +[](monad_async_task task) -> monad_async_result {
                *(int *)task->user_ptr = 1;
                EXPECT_EQ(task->current_executor->current_task, task);
                EXPECT_EQ(task->current_executor->tasks_pending_launch, 0);
                EXPECT_EQ(task->current_executor->tasks_running, 1);
                EXPECT_EQ(task->current_executor->tasks_suspended, 0);
                CHECK_RESULT(monad_async_task_suspend_for_duration(
                    task, 1000)); // one microsecond
                *(int *)task->user_ptr = 2;
                EXPECT_EQ(task->current_executor->current_task, task);
                EXPECT_EQ(task->current_executor->tasks_pending_launch, 0);
                EXPECT_EQ(task->current_executor->tasks_running, 1);
                EXPECT_EQ(task->current_executor->tasks_suspended, 0);
                return monad_async_make_success(5);
            };
            r = monad_async_task_attach(ex.get(), t1.get(), nullptr);
            CHECK_RESULT(r);
            EXPECT_TRUE(t1->is_pending_launch);
            EXPECT_FALSE(t1->is_running);
            EXPECT_FALSE(t1->is_suspended_awaiting);
            EXPECT_FALSE(t1->is_suspended_completed);
            EXPECT_EQ(ex->current_task, nullptr);
            EXPECT_EQ(ex->tasks_pending_launch, 1);
            EXPECT_EQ(ex->tasks_running, 0);
            EXPECT_EQ(ex->tasks_suspended, 0);
            ts.tv_sec = 3; // timeout and fail the test after this
            r = monad_async_executor_run(ex.get(), 1, &ts); // runs and suspends
            monad_async_cpu_ticks_count_t const ticks_when_resumed =
                t1->ticks_when_resumed;
            EXPECT_EQ(did_run, 1);
            EXPECT_EQ(ex->tasks_pending_launch, 0);
            EXPECT_EQ(ex->tasks_running, 0);
            EXPECT_EQ(ex->tasks_suspended, 1);
            CHECK_RESULT(r);
            EXPECT_EQ(r.value, 1);
            EXPECT_FALSE(t1->is_pending_launch);
            EXPECT_FALSE(t1->is_running);
            EXPECT_TRUE(t1->is_suspended_awaiting);
            EXPECT_FALSE(t1->is_suspended_completed);
            r = monad_async_executor_run(ex.get(), 1, &ts); // resumes and exits
            EXPECT_EQ(did_run, 2);
            EXPECT_EQ(ex->tasks_pending_launch, 0);
            EXPECT_EQ(ex->tasks_running, 0);
            EXPECT_EQ(ex->tasks_suspended, 0);
            CHECK_RESULT(r);
            EXPECT_EQ(r.value, 1);
            EXPECT_FALSE(t1->is_pending_launch);
            EXPECT_FALSE(t1->is_running);
            EXPECT_FALSE(t1->is_suspended_awaiting);
            EXPECT_FALSE(t1->is_suspended_completed);
            CHECK_RESULT(t1->result);
            EXPECT_EQ(t1->result.value, 5);
            if (n == 9) {
                std::cout << "\n   Task attach to task initiate took "
                          << (ticks_when_resumed - t1->ticks_when_attached)
                          << " ticks.";
                std::cout << "\n   Task initiate to task suspend await took "
                          << (t1->ticks_when_suspended_awaiting -
                              ticks_when_resumed)
                          << " ticks.";
                std::cout
                    << "\n   Task suspend await to task suspend completed took "
                    << (t1->ticks_when_suspended_completed -
                        t1->ticks_when_suspended_awaiting)
                    << " ticks.";
                std::cout << "\n   Task suspend completed to task resume took "
                          << (t1->ticks_when_resumed -
                              t1->ticks_when_suspended_completed)
                          << " ticks.";
                std::cout << "\n   Task resume to task detach took "
                          << (t1->ticks_when_detached - t1->ticks_when_resumed)
                          << " ticks.";
                std::cout << "\n   Task executed for a total of "
                          << t1->total_ticks_executed << " ticks." << std::endl;
            }
        }
    }

    {
        auto cs = make_context_switcher(monad_async_context_switcher_none);

        struct shared_t
        {
            uint64_t ops{0};
        } shared;

        auto func = +[](monad_async_task task) -> monad_async_result {
            auto *shared = (shared_t *)task->user_ptr;
            shared->ops++;
            return monad_async_make_success(0);
        };
        std::vector<task_ptr> tasks;
        tasks.reserve(1024);
        for (size_t n = 0; n < 1024; n++) {
            tasks.push_back(make_task(cs.get(), t_attr));
            tasks.back()->user_code = func;
            tasks.back()->user_ptr = (void *)&shared;
        }
        auto const begin = std::chrono::steady_clock::now();
        do {
            for (auto &i : tasks) {
                auto r = monad_async_task_attach(ex.get(), i.get(), nullptr);
                CHECK_RESULT(r);
            }
            auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
            CHECK_RESULT(r);
            if (r.value != 1024) {
                abort();
            }
        }
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(3));
        while (ex->tasks_running > 0 || ex->tasks_suspended > 0) {
            auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
            CHECK_RESULT(r);
        }
        auto const end = std::chrono::steady_clock::now();
        std::cout
            << "\n\n   Initiated, executed and tore down "
            << (1000.0 * double(shared.ops) /
                double(std::chrono::duration_cast<std::chrono::milliseconds>(
                           end - begin)
                           .count()))
            << " ops/sec which is "
            << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count()) /
                double(shared.ops))
            << " ns/op." << std::endl;
    }

    {
        auto cs = make_context_switcher(monad_async_context_switcher_sjlj);

        struct shared_t
        {
            uint64_t ops{0};
            bool done;
        } shared;

        auto func = +[](monad_async_task task) -> monad_async_result {
            auto *shared = (shared_t *)task->user_ptr;
            while (!shared->done) {
                shared->ops++;
                auto r = monad_async_task_suspend_for_duration(task, 0);
                CHECK_RESULT(r);
            }
            return monad_async_make_success(0);
        };
        std::vector<task_ptr> tasks;
        tasks.reserve(64);
        for (size_t n = 0; n < 64; n++) {
            tasks.push_back(make_task(cs.get(), t_attr));
            tasks.back()->user_code = func;
            tasks.back()->user_ptr = (void *)&shared;
            auto r =
                monad_async_task_attach(ex.get(), tasks.back().get(), nullptr);
            CHECK_RESULT(r);
        }
        auto const begin = std::chrono::steady_clock::now();
        do {
            auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
            CHECK_RESULT(r);
        }
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(3));
        auto const end = std::chrono::steady_clock::now();
        shared.done = true;
        while (ex->tasks_running > 0 || ex->tasks_suspended > 0) {
            auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
            CHECK_RESULT(r);
        }
        std::cout
            << "\n\n   Suspend-resume "
            << (1000.0 * double(shared.ops) /
                double(std::chrono::duration_cast<std::chrono::milliseconds>(
                           end - begin)
                           .count()))
            << " ops/sec which is "
            << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count()) /
                double(shared.ops))
            << " ns/op." << std::endl;
    }
}
