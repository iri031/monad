#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/file_io.h"
#include "monad/async/util.h"

#include <chrono>
#include <filesystem>
#include <fstream>

#include <fcntl.h>
#include <unistd.h>

TEST(file_io, works)
{
    struct shared_state_t
    {
        char tempfilepath[256];

        shared_state_t()
        {
            int fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            if (-1 == write(fd, "hello world", 11)) {
                abort();
            }
            close(fd);
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_async_result task(monad_async_task task)
        {
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
                &iostatus[0], task, fh.get(), &iov[0], 1, 0, 0);
            monad_async_task_file_read(
                &iostatus[1], task, fh.get(), &iov[1], 1, 6, 0);
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

            fh.reset();
            std::cout << "   Closing the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;
            return monad_async_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and a task, and attach the task to the executor
    auto s = make_context_switcher(monad_async_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t = make_task(s.get(), t_attr);
    t->user_ptr = (void *)&shared_state;
    t->user_code = +[](monad_async_task task) -> monad_async_result {
        return ((shared_state_t *)task->user_ptr)->task(task);
    };
    to_result(monad_async_task_attach(ex.get(), t.get(), nullptr)).value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
}
