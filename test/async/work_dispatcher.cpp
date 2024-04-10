#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/work_dispatcher.h"

#include <chrono>
#include <thread>
#include <vector>

#include <pthread.h>

TEST(work_dispatcher, works)
{
    return; // not implemented yet

    struct thread_state
    {
        std::thread thread;

        explicit thread_state(monad_async_work_dispatcher wd)
            : thread(&thread_state::run, this, wd)
        {
        }

        void run(monad_async_work_dispatcher wd)
        {
            struct monad_async_work_dispatcher_executor_attr ex_attr
            {
            };

            auto ex = make_work_dispatcher_executor(wd, ex_attr);
            for (;;) {
                auto r = monad_async_work_dispatcher_executor_run(ex.get());
                CHECK_RESULT(r);
                if (r.value < 0) {
                    break;
                }
            }
        }
    };

    struct monad_async_work_dispatcher_attr wd_attr
    {
    };

    auto wd = make_work_dispatcher(wd_attr);
    std::vector<thread_state> threads;

    for (size_t n = 0; n < std::thread::hardware_concurrency(); n++) {
        threads.emplace_back(thread_state(wd.get()));
    }

    struct task_state
    {
        task_ptr task;
        unsigned ops{0};
        bool done{true};

        task_state(monad_async_context_switcher switcher)
            : task([&] {
                monad_async_task_attr t_attr{};
                return make_task(switcher, t_attr);
            }())
        {
        }

        void run()
        {
            ops++;
            done = true;
        }

        static monad_async_result run(monad_async_task task)
        {
            ((task_state *)task->user_ptr)->run();
            return monad_async_make_success(0);
        }
    };

    auto cs = make_context_switcher(monad_async_context_switcher_none);
    std::vector<task_state> tasks;
    for (size_t n = 0; n < 1024; n++) {
        tasks.emplace_back(cs.get());
    }

    std::vector<monad_async_task> task_ptrs;
    task_ptrs.resize(tasks.size());

    auto const begin = std::chrono::steady_clock::now();
    do {
        for (size_t n = 0; n < tasks.size(); n++) {
            if (tasks[n].done) {
                task_ptrs[n] = tasks[n].task.get();
                tasks[n].done = false;
            }
            else {
                task_ptrs[n] = nullptr;
            }
        }
        CHECK_RESULT(monad_async_work_dispatcher_submit(
            wd.get(), task_ptrs.data(), task_ptrs.size()));
    }
    while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(5));

    auto const end = std::chrono::steady_clock::now();
    uint64_t ops = 0;
    for (auto &i : tasks) {
        ops += i.ops;
    }
}
