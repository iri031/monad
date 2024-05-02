#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/executor.h"

#include "monad/async/task.h"

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <thread>
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
            auto *current_executor =
                task->current_executor.load(std::memory_order_acquire);
            EXPECT_EQ(current_executor->current_task, task);
            EXPECT_EQ(current_executor->tasks_pending_launch, 0);
            EXPECT_EQ(current_executor->tasks_running, 1);
            EXPECT_EQ(current_executor->tasks_suspended, 0);
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
                auto *current_executor =
                    task->current_executor.load(std::memory_order_acquire);
                EXPECT_EQ(current_executor->current_task, task);
                EXPECT_EQ(current_executor->tasks_pending_launch, 0);
                EXPECT_EQ(current_executor->tasks_running, 1);
                EXPECT_EQ(current_executor->tasks_suspended, 0);
                CHECK_RESULT(monad_async_task_suspend_for_duration(
                    nullptr, task, 1000)); // one microsecond
                *(int *)task->user_ptr = 2;
                current_executor =
                    task->current_executor.load(std::memory_order_acquire);
                EXPECT_EQ(current_executor->current_task, task);
                EXPECT_EQ(current_executor->tasks_pending_launch, 0);
                EXPECT_EQ(current_executor->tasks_running, 1);
                EXPECT_EQ(current_executor->tasks_suspended, 0);
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
                auto r =
                    monad_async_task_suspend_for_duration(nullptr, task, 0);
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

TEST(executor, foreign_thread)
{
    struct executor_thread
    {
        executor_ptr executor;
        std::thread thread;
        uint32_t ops{0};
    };

    std::vector<executor_thread> executor_threads{
        std::thread::hardware_concurrency()};
    std::atomic<int> latch{0};
    for (size_t n = 0; n < executor_threads.size(); n++) {
        executor_threads[n].thread = std::thread(
            [&latch](executor_thread *state) {
                monad_async_executor_attr ex_attr{};
                state->executor = make_executor(ex_attr);
                latch++;
                for (;;) {
                    auto r = to_result(monad_async_executor_run(
                        state->executor.get(), size_t(-1), nullptr));
                    if (!r) {
                        if (r.assume_error() == errc::operation_canceled) {
                            break;
                        }
                        std::cerr
                            << "FATAL: " << r.assume_error().message().c_str()
                            << std::endl;
                        abort();
                    }
                    state->ops += uint32_t(r.assume_value());
                }
                state->executor.reset();
            },
            &executor_threads[n]);
    }

    static bool checking = false;

    struct task
    {
        task_ptr task;
        uint32_t ops{0};

        static monad_async_result run(monad_async_task t)
        {
            auto *self = (struct task *)t->user_ptr;
            self->ops++;
            if (checking) {
                EXPECT_EQ(self->ops, 1);
                EXPECT_EQ(
                    t->current_executor.load(std::memory_order_acquire)
                        ->current_task,
                    t);
                EXPECT_FALSE(t->is_awaiting_dispatch);
                EXPECT_FALSE(t->is_pending_launch);
                EXPECT_TRUE(t->is_running);
                EXPECT_FALSE(t->is_suspended_awaiting);
                EXPECT_FALSE(t->is_suspended_completed);
            }
            return monad_async_make_success(0);
        }
    };

    std::vector<task> tasks(1024);
    monad_async_context_switcher none_switcher;
    CHECK_RESULT(monad_async_context_switcher_none_create(&none_switcher));
    monad_async_task_attr attr{};
    for (auto &i : tasks) {
        i.task = make_task(none_switcher, attr);
        i.task->user_code = task::run;
        i.task->user_ptr = (void *)&i;
    }
    while (latch < (int)executor_threads.size()) {
        std::this_thread::yield();
    }

    {
        auto *task = tasks.front().task.get();
        auto *ex = executor_threads.front().executor.get();
        EXPECT_EQ(tasks.front().ops, 0);
        EXPECT_EQ(task->current_executor, nullptr);
        EXPECT_FALSE(task->is_awaiting_dispatch);
        EXPECT_FALSE(task->is_pending_launch);
        EXPECT_FALSE(task->is_running);
        EXPECT_FALSE(task->is_suspended_awaiting);
        EXPECT_FALSE(task->is_suspended_completed);
        CHECK_RESULT(monad_async_task_attach(ex, task, nullptr));
        EXPECT_TRUE(task->is_pending_launch || task->is_running);
        EXPECT_TRUE(ex->tasks_pending_launch > 0 || ex->tasks_running > 0);
        while (task->is_pending_launch || task->is_running ||
               ex->tasks_running > 0) {
            std::this_thread::yield();
        }
        EXPECT_EQ(ex->tasks_pending_launch, 0);
        EXPECT_EQ(ex->tasks_running, 0);
        EXPECT_FALSE(task->is_awaiting_dispatch);
        EXPECT_FALSE(task->is_pending_launch);
        EXPECT_FALSE(task->is_running);
        EXPECT_FALSE(task->is_suspended_awaiting);
        EXPECT_FALSE(task->is_suspended_completed);
        EXPECT_EQ(tasks.front().ops, 1);
    }
    checking = false;

    auto const begin = std::chrono::steady_clock::now();
    size_t n = 0;
    do {
        for (auto &i : tasks) {
            if (i.task->current_executor == nullptr) {
                CHECK_RESULT(monad_async_task_attach(
                    executor_threads[n++].executor.get(),
                    i.task.get(),
                    nullptr));
                if (n >= executor_threads.size()) {
                    n = 0;
                }
            }
        }
    }
    while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(5));
    auto cancelled = monad_async_make_failure(ECANCELED);
    for (auto &i : executor_threads) {
        CHECK_RESULT(monad_async_executor_wake(i.executor.get(), &cancelled));
        i.thread.join();
    }
    auto const end = std::chrono::steady_clock::now();
    auto const diff =
        double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count());
    uint64_t executor_ops = 0;
    for (auto &i : executor_threads) {
        executor_ops += i.ops;
    }
    uint64_t task_ops = 0;
    for (auto &i : tasks) {
        task_ops += i.ops;
    }
    EXPECT_EQ(executor_ops, task_ops);
    std::cout << "   Executed " << task_ops << " tasks on "
              << executor_threads.size() << " kernel threads at "
              << (1000000000.0 * double(task_ops) / diff) << " ops/sec ("
              << (diff / double(task_ops)) << " ns/op)" << std::endl;
}
