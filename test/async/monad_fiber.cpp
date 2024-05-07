#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/file_io.h"
#include "monad/async/util.h"
#include "monad/fiber/scheduler.h"

#include <chrono>
#include <filesystem>

#include <fcntl.h>
#include <unistd.h>

TEST(monad_fiber, works)
{
    return; // not finished

    struct shared_state_t
    {
        char tempfilepath[256];
        pid_t io_executor_tid;
        std::atomic<bool> done{false};

        shared_state_t()
        {
            int fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            if (-1 == write(fd, "hello world", 11)) {
                abort();
            }
            close(fd);
            io_executor_tid = gettid();
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_async_result task(monad_async_task task)
        {
            // We need to be initially executing on the compute executor
            if (gettid() == io_executor_tid) {
                abort();
            }

            // Before we can do i/o, we need to transfer ourselves to the i/o
            // executor
            // TODO

            // Open the file
            struct open_how how
            {
                .flags = O_RDONLY, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            EXPECT_EQ(fh->executor, task->current_executor);
            std::cout << "   Opening the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            char buffer[64]{};
            // Initiate two concurrent reads
            monad_async_io_status iostatus[2]{};
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[1]));
            struct iovec iov[] = {
                {.iov_base = buffer, .iov_len = 6},
                {.iov_base = buffer + 6, .iov_len = 6}};
            monad_async_task_file_read(
                &iostatus[0], task, fh.get(), 0, &iov[0], 1, 0, 0);
            monad_async_task_file_read(
                &iostatus[1], task, fh.get(), 0, &iov[1], 1, 6, 0);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus[1]));
            EXPECT_EQ(task->io_submitted, 2);
            EXPECT_EQ(task->io_completed_not_reaped, 0);

            // Wait until both reads have completed
            while (monad_async_io_in_progress(iostatus, 2) > 0) {
                monad_async_io_status *completed = nullptr;
                to_result(monad_async_task_suspend_for_duration(
                              &completed, task, (uint64_t)-1))
                    .value();
                EXPECT_TRUE(
                    completed == &iostatus[0] || completed == &iostatus[1]);
            }
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 2);

            // Iterate through all completed i/o for this task
            for (auto *completed = monad_async_task_completed_io(task);
                 completed != nullptr;
                 completed = monad_async_task_completed_io(task)) {
                EXPECT_TRUE(to_result(completed->result).has_value());
            }
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);

            fh.reset();
            std::cout << "   Closing the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Transfer ourselves back to the compute executor
            // TODO

            EXPECT_STREQ(buffer, "hello world");
            EXPECT_EQ(to_result(iostatus[0].result).value(), 6);
            EXPECT_EQ(to_result(iostatus[1].result).value(), 5);
            std::cout << "   The first read took "
                      << (iostatus[0].ticks_when_completed -
                          iostatus[0].ticks_when_initiated)
                      << " ticks." << std::endl;
            std::cout << "   The second read took "
                      << (iostatus[1].ticks_when_completed -
                          iostatus[1].ticks_when_initiated)
                      << " ticks." << std::endl;
            done = true;
            return monad_async_make_success(0);
        }
    } shared_state;

    // Make a compute executor of four kernel threads
    monad_fiber_scheduler_t compute_ex;
    monad_fiber_scheduler_create(&compute_ex, 4);

    // Make an i/o executor
    monad_async_executor_attr io_ex_attr{};
    io_ex_attr.io_uring_ring.entries = 64;
    auto io_ex = make_executor(io_ex_attr);

    // Make a context switcher and a task
    auto s = make_context_switcher(monad_async_context_switcher_fiber);
    monad_async_task_attr t_attr{};
    auto io_task = make_task(s.get(), t_attr);
    io_task->user_ptr = (void *)&shared_state;
    io_task->user_code = +[](monad_async_task task) -> monad_async_result {
        return ((shared_state_t *)task->user_ptr)->task(task);
    };

    // Post the task onto the compute executor
    monad_fiber_scheduler_post(
        &compute_ex, monad_fiber_task_from_async_task(io_task.get()), 0);

    // The task will initiate some i/o. This will cause it to take itself off
    // the compute executor and attach itself to the i/o executor, which runs in
    // this thread, so we need to pump the i/o executor from here.
    struct timespec ts
    {
        .tv_sec = 1, .tv_nsec = 0
    };

    while (!shared_state.done) {
        auto r =
            to_result(monad_async_executor_run(io_ex.get(), size_t(-1), &ts));
        if (!r) {
            if (r.error() != errc::timed_out) {
                r.value();
            }
        }
    }
}
