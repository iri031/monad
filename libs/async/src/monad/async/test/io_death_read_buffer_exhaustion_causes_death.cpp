
#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/connected_operation.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/assert.h>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>

#include <gtest/gtest.h>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <csignal>
#include <cstddef>
#include <iostream>
#include <memory>
#include <utility>
#include <vector>

namespace
{
    TEST(AsyncIODeathTest, read_buffer_exhaustion_causes_death)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring1;
        monad::io::Ring testring2(1);
        monad::io::Buffers testrwbuf = make_buffers_for_segregated_read_write(
            testring1,
            testring2,
            1,
            1,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);
        std::vector<monad::async::read_single_buffer_sender::buffer_type> bufs;
        auto empty_testio = monad::make_scope_exit(
            [&]() noexcept { testio.wait_until_done(); });

        struct empty_receiver
        {
            std::vector<monad::async::read_single_buffer_sender::buffer_type>
                &bufs;

            void set_value(
                monad::async::erased_connected_operation *,
                monad::async::read_single_buffer_sender::result_type r)
            {
                MONAD_ASSERT(r);
                // Exactly the same test as the death test, except for this line
                bufs.emplace_back(std::move(r.assume_value().get()));
            }
        };

        auto make = [&] {
            auto state(testio.make_connected(
                monad::async::read_single_buffer_sender(
                    {0, 0}, monad::async::DISK_PAGE_SIZE),
                empty_receiver{bufs}));
            state->initiate(); // will reap completions if no buffers free
            state.release();
        };
        for (size_t n = 0; n < 512; n++) {
            make();
        }
        std::cerr << "Must fail after this:" << std::endl;
        make();
    }
}
