#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/socket_io.h"

#include <netinet/in.h>

TEST(socket_io, unregistered_buffers)
{
    struct shared_state_t
    {
        uint16_t localhost_port{0};

        monad_async_result server(monad_async_task task)
        {
            try {
                // Open a listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);

                struct sockaddr_in localhost
                {
                    .sin_family = AF_INET, .sin_port = 0 /* any */,
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)}, .sin_zero
                    {
                    }
                };

                to_result(
                    monad_async_task_socket_bind(
                        sock.get(), (sockaddr *)&localhost, sizeof(localhost)))
                    .value();
                to_result(monad_async_task_socket_listen(sock.get(), 0))
                    .value();
                localhost_port =
                    ntohs(((struct sockaddr_in *)&sock->addr)->sin_port);
                std::cout << "   Server socket listens on port "
                          << localhost_port << std::endl;
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();

                std::cout << "   Server initiates accepting new connections."
                          << std::endl;
                // Accept new connections, suspending until a new one appears
                socket_ptr conn([&] {
                    monad_async_socket conn;
                    to_result(monad_async_task_socket_accept(
                                  &conn, task, sock.get(), 0))
                        .value();
                    return socket_ptr(conn, socket_deleter{task});
                }());
                // Close the listening socket
                sock.reset();
                auto *peer = (struct sockaddr_in *)&conn->addr;
                std::cout << "   Server accepts new connection from 0x"
                          << std::hex << peer->sin_addr.s_addr << std::dec
                          << ":" << peer->sin_port << std::endl;

                std::cout << "   Server initiates write to socket."
                          << std::endl;
                // Write "hello world" to the connecting socket
                monad_async_io_status status;
                struct iovec iov[] = {{(void *)"hello world", 11}};
                struct msghdr msg = {};
                msg.msg_iov = iov;
                msg.msg_iovlen = 1;
                monad_async_task_socket_send(
                    &status, task, conn.get(), 0, &msg, 0);
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto byteswritten = to_result(status.result).value();
                std::cout << "   Server writes " << byteswritten
                          << " bytes to socket." << std::endl;

                std::cout << "   Server initiates shutdown of socket."
                          << std::endl;
                // Ensure written data gets flushed out.
                monad_async_task_socket_shutdown(
                    &status, task, conn.get(), SHUT_RDWR);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                to_result(status.result).value();
                std::cout << "   Server has shutdown socket." << std::endl;
                return monad_async_make_success(0);
            }
            catch (std::exception const &e) {
                std::cerr << "FATAL: " << e.what() << std::endl;
                std::terminate();
            }
        }

        monad_async_result client(monad_async_task task)
        {
            try {
                // Connect to the listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();

                monad_async_io_status status;

                struct sockaddr_in addr
                {
                    .sin_family = AF_INET, .sin_port = htons(localhost_port),
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)}, .sin_zero
                    {
                    }
                };

                std::cout << "   Client connects to port " << localhost_port
                          << "." << std::endl;
                monad_async_task_socket_connect(
                    &status, task, sock.get(), (sockaddr *)&addr, sizeof(addr));
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                std::cout << "   Client has connected." << std::endl;

                // Read from the socket
                std::cout << "   Client initiates read of socket." << std::endl;
                char buffer[256]{};
                struct iovec iov[] = {{(void *)buffer, 256}};
                struct msghdr msg = {};
                msg.msg_iov = iov;
                msg.msg_iovlen = 1;
                monad_async_task_socket_recv(
                    &status, task, sock.get(), 0, &msg, 0);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                auto bytesread = to_result(status.result).value();

                std::cout << "   Client reads " << bytesread
                          << " bytes which are '" << (char *)iov[0].iov_base
                          << "'." << std::endl;
                EXPECT_EQ(bytesread, 11);
                EXPECT_STREQ((char *)iov[0].iov_base, "hello world");

                std::cout << "   Client initiates shutdown of socket."
                          << std::endl;
                // Gracefully close the socket
                monad_async_task_socket_shutdown(
                    &status, task, sock.get(), SHUT_RDWR);
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, uint64_t(-1)))
                    .value();
                to_result(status.result).value();
                std::cout << "   Client has shutdown socket." << std::endl;
                return monad_async_make_success(0);
            }
            catch (std::exception const &e) {
                std::cerr << "FATAL: " << e.what() << std::endl;
                std::terminate();
            }
        }
    }

    shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and two tasks, and attach the tasks to the
    // executor
    auto s = make_context_switcher(monad_async_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t_server = make_task(s.get(), t_attr);
    t_server->user_ptr = (void *)&shared_state;
    t_server->user_code = +[](monad_async_task task) -> monad_async_result {
        return ((shared_state_t *)task->user_ptr)->server(task);
    };
    to_result(monad_async_task_attach(ex.get(), t_server.get(), nullptr))
        .value();
    auto t_client = make_task(s.get(), t_attr);
    t_client->user_ptr = (void *)&shared_state;
    t_client->user_code = +[](monad_async_task task) -> monad_async_result {
        return ((shared_state_t *)task->user_ptr)->client(task);
    };
    to_result(monad_async_task_attach(ex.get(), t_client.get(), nullptr))
        .value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
}

#if 0
TEST(file_io, registered_buffers)
{
    struct shared_state_t
    {
        char tempfilepath[256];

        shared_state_t()
        {
            int fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
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
                .flags = O_RDWR, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            EXPECT_EQ(fh->executor, task->current_executor);
            std::cout << "   Opening the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Write to the file
            {
                monad_async_executor_registered_io_buffer buffer;
                to_result(monad_async_executor_claim_registered_io_buffer(
                              &buffer, task->current_executor, 4097, true))
                    .value();
                monad_async_io_status iostatus{};
                memcpy(buffer.iov->iov_base, "hello world", 11);
                EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
                struct iovec iov[] = {
                    {.iov_base = buffer.iov[0].iov_base, .iov_len = 11}};
                monad_async_task_file_write(
                    &iostatus, task, fh.get(), buffer.index, &iov[0], 1, 0, 0);
                EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
                EXPECT_EQ(task->io_submitted, 1);
                EXPECT_EQ(task->io_completed_not_reaped, 0);
                monad_async_io_status *completed = nullptr;
                EXPECT_EQ(
                    to_result(monad_async_task_suspend_until_completed_io(
                                  &completed, task, (uint64_t)-1))
                        .value(),
                    1);
                EXPECT_EQ(task->io_submitted, 0);
                EXPECT_EQ(task->io_completed_not_reaped, 0);
                EXPECT_EQ(completed, &iostatus);
                EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
                to_result(iostatus.result).value();
                std::cout << "   The write took "
                          << (iostatus.ticks_when_completed -
                              iostatus.ticks_when_initiated)
                          << " ticks." << std::endl;
                to_result(monad_async_executor_release_registered_io_buffer(
                              task->current_executor, buffer.index))
                    .value();
            }

            // Get my registered buffer
            monad_async_executor_registered_io_buffer buffer;
            to_result(monad_async_executor_claim_registered_io_buffer(
                          &buffer, task->current_executor, 4097, false))
                .value();
            // Initiate two concurrent reads
            monad_async_io_status iostatus[2]{};
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[1]));
            struct iovec iov[] = {
                {.iov_base = buffer.iov[0].iov_base, .iov_len = 6},
                {.iov_base = (char *)buffer.iov[0].iov_base + 6, .iov_len = 6}};
            monad_async_task_file_read(
                &iostatus[0], task, fh.get(), buffer.index, &iov[0], 1, 0, 0);
            monad_async_task_file_read(
                &iostatus[1], task, fh.get(), buffer.index, &iov[1], 1, 6, 0);
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

            EXPECT_STREQ((char const *)buffer.iov[0].iov_base, "hello world");
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

            to_result(monad_async_executor_release_registered_io_buffer(
                          task->current_executor, buffer.index))
                .value();
            return monad_async_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    ex_attr.io_uring_ring.registered_buffers.large = 1;
    ex_attr.io_uring_wr_ring.entries = 8;
    ex_attr.io_uring_wr_ring.registered_buffers.large = 1;
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

TEST(file_io, misc_ops)
{
    struct shared_state_t
    {
        char tempfilepath[256];

        shared_state_t()
        {
            int fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
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
                .flags = O_RDWR, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            EXPECT_EQ(fh->executor, task->current_executor);
            std::cout << "   Opening the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Preallocate the contents
            to_result(monad_async_task_file_fallocate(
                          task, fh.get(), FALLOC_FL_ZERO_RANGE, 0, 11))
                .value();
            std::cout << "   Preallocating the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Write to the file
            monad_async_io_status iostatus{};
            struct iovec iov[] = {
                {.iov_base = (void *)"hello world", .iov_len = 11}};
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            monad_async_task_file_write(
                &iostatus, task, fh.get(), 0, &iov[0], 1, 0, 0);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
            EXPECT_EQ(task->io_submitted, 1);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            monad_async_io_status *completed = nullptr;
            EXPECT_EQ(
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value(),
                1);
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            EXPECT_EQ(completed, &iostatus);
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            to_result(iostatus.result).value();
            std::cout << "   The write took "
                      << (iostatus.ticks_when_completed -
                          iostatus.ticks_when_initiated)
                      << " ticks." << std::endl;

            // Initialise sync to disc for the range without waiting for it to
            // reach the disc
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            monad_async_task_file_range_sync(
                &iostatus,
                task,
                fh.get(),
                0,
                11,
                SYNC_FILE_RANGE_WAIT_BEFORE | SYNC_FILE_RANGE_WRITE);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
            EXPECT_EQ(task->io_submitted, 1);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            completed = nullptr;
            EXPECT_EQ(
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value(),
                1);
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            EXPECT_EQ(completed, &iostatus);
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            to_result(iostatus.result).value();
            std::cout << "   The write barrier took "
                      << (iostatus.ticks_when_completed -
                          iostatus.ticks_when_initiated)
                      << " ticks." << std::endl;

            // Synchronise the writes to the file fully with storage in a sudden
            // power loss retrievable way
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            monad_async_task_file_durable_sync(&iostatus, task, fh.get());
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
            EXPECT_EQ(task->io_submitted, 1);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            completed = nullptr;
            EXPECT_EQ(
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value(),
                1);
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            EXPECT_EQ(completed, &iostatus);
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            to_result(iostatus.result).value();
            std::cout << "   The durable sync took "
                      << (iostatus.ticks_when_completed -
                          iostatus.ticks_when_initiated)
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
    ex_attr.io_uring_ring.entries = 8;
    ex_attr.io_uring_wr_ring.entries = 8;
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

TEST(file_io, benchmark)
{
    struct shared_state_t
    {
        char tempfilepath[256];
        bool done{false};

        shared_state_t()
        {
            int fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            static constexpr std::string_view text(
                R"(Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.
      Sed ut perspiciatis unde omnis iste natus error sit voluptatem accusantium doloremque laudantium, totam rem aperiam, eaque ipsa quae ab illo inventore veritatis et quasi architecto beatae vitae dicta sunt explicabo. Nemo enim ipsam voluptatem quia voluptas sit aspernatur aut odit aut fugit, sed quia consequuntur magni dolores eos qui ratione voluptatem sequi nesciunt. Neque porro quisquam est, qui dolorem ipsum quia dolor sit amet, consectetur, adipisci velit, sed quia non numquam eius modi tempora incidunt ut labore et dolore magnam aliquam quaerat voluptatem. Ut enim ad minima veniam, quis nostrum exercitationem ullam corporis suscipit laboriosam, nisi ut aliquid ex ea commodi consequatur? Quis autem vel eum iure reprehenderit qui in ea voluptate velit esse quam nihil molestiae consequatur, vel illum qui dolorem eum fugiat quo voluptas nulla pariatur?
)");
            for (size_t length = 0; length < 64 * 512; length += text.size()) {
                if (-1 == write(fd, text.data(), text.size())) {
                    abort();
                }
            }
            close(fd);
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_async_result
        task(monad_async_task task, monad_async_priority priority)
        {
            to_result(monad_async_task_set_priorities(
                          task, priority, monad_async_priority_unchanged))
                .value();

            // Open the file
            struct open_how how
            {
                .flags = O_RDONLY | O_DIRECT, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            monad_async_executor_registered_io_buffer buffer;
            to_result(monad_async_executor_claim_registered_io_buffer(
                          &buffer, task->current_executor, 1, false))
                .value();
            std::vector<monad_async_io_status> iostatus(128);
            uint32_t ops = 0;

            auto const begin = std::chrono::steady_clock::now();
            for (size_t n = 0; n < iostatus.size(); n++) {
                struct iovec iov[] = {
                    {.iov_base = (void *)((std::byte *)buffer.iov[0].iov_base +
                                          n * 512),
                     .iov_len = 512}};
                monad_async_task_file_read(
                    &iostatus[n],
                    task,
                    fh.get(),
                    buffer.index,
                    iov,
                    1,
                    n * 512,
                    0);
            }
            while (!done) {
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value();
                auto idx = size_t(completed - iostatus.data());
                struct iovec iov[] = {
                    {.iov_base = (void *)((std::byte *)buffer.iov[0].iov_base +
                                          idx * 512),
                     .iov_len = 512}};
                monad_async_task_file_read(
                    completed,
                    task,
                    fh.get(),
                    buffer.index,
                    iov,
                    1,
                    idx * 512,
                    0);
                ops++;
            }
            for (;;) {
                monad_async_io_status *completed;
                if (to_result(monad_async_task_suspend_until_completed_io(
                                  &completed, task, 0))
                        .value() == 0) {
                    break;
                }
                ops++;
            }
            auto const end = std::chrono::steady_clock::now();
            to_result(monad_async_executor_release_registered_io_buffer(
                          task->current_executor, buffer.index))
                .value();
            auto const diff =
                double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count());
            std::cout << "   Task priority " << (int)priority << " did " << ops
                      << " read i/o which is "
                      << (1000000000.0 * (double)ops / diff)
                      << " ops/sec (which is " << (diff / (double)ops)
                      << " ns/op)" << std::endl;
            return monad_async_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 128;
    ex_attr.io_uring_ring.registered_buffers.small = 2;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and two tasks which do the same thing, but with
    // different priority
    auto s = make_context_switcher(monad_async_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t1 = make_task(s.get(), t_attr);
    t1->user_ptr = (void *)&shared_state;
    t1->user_code = +[](monad_async_task task) -> monad_async_result {
        return ((shared_state_t *)task->user_ptr)
            ->task(task, monad_async_priority_normal);
    };
    auto t2 = make_task(s.get(), t_attr);
    t2->user_ptr = (void *)&shared_state;
    t2->user_code = +[](monad_async_task task) -> monad_async_result {
        return ((shared_state_t *)task->user_ptr)
            ->task(task, monad_async_priority_high);
    };
    to_result(monad_async_task_attach(ex.get(), t1.get(), nullptr)).value();
    to_result(monad_async_task_attach(ex.get(), t2.get(), nullptr)).value();

    // Run the executor for five seconds
    auto const begin = std::chrono::steady_clock::now();
    for (;;) {
        to_result(monad_async_executor_run(ex.get(), 1024, nullptr)).value();
        if (std::chrono::steady_clock::now() - begin >=
            std::chrono::seconds(5)) {
            break;
        }
    }
    shared_state.done = true;

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
}
#endif
