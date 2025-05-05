#include "gtest/gtest.h"

#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/connected_operation.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/array.hpp>
#include <monad/core/assert.h>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <chrono>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
#include <system_error>
#include <utility>
#include <vector>

#include <unistd.h>

namespace
{
    TEST(AsyncIO, buffer_exhaustion_pauses_until_io_completes_write)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring1;
        monad::io::Ring testring2(1);
        monad::io::Buffers testrwbuf =
            monad::io::make_buffers_for_segregated_read_write(
                testring1,
                testring2,
                1,
                1,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);

        struct empty_receiver
        {
            void set_value(
                monad::async::erased_connected_operation *,
                monad::async::write_single_buffer_sender::result_type r)
            {
                MONAD_ASSERT(r);
            }
        };

        for (size_t n = 0; n < 10; n++) {
            auto state(testio.make_connected(
                monad::async::write_single_buffer_sender(
                    {0, 0}, monad::async::DISK_PAGE_SIZE),
                empty_receiver{}));
            // Exactly the same test as the death test, except for this line
            state->initiate(); // will reap completions if no buffers free
            state.release();
        }
        testio.wait_until_done();
    }

    TEST(AsyncIO, buffer_exhaustion_pauses_until_io_completes_read)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring;
        monad::io::Buffers testrwbuf = monad::io::make_buffers_for_read_only(
            testring, 1, monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);
        static std::vector<monad::async::read_single_buffer_sender::buffer_type>
            bufs;

        struct empty_receiver
        {
            std::vector<monad::async::read_single_buffer_sender::buffer_type>
                &bufs;

            enum
            {
                lifetime_managed_internally = true
            };

            void set_value(
                monad::async::erased_connected_operation *,
                monad::async::read_single_buffer_sender::result_type r)
            {
                MONAD_ASSERT(r);
                // Exactly the same test as the death test, except for this line
                // bufs.emplace_back(std::move(r.assume_value().get()));
            }
        };

        for (size_t n = 0; n < 1000; n++) {
            auto state(testio.make_connected(
                monad::async::read_single_buffer_sender(
                    {0, 0}, monad::async::DISK_PAGE_SIZE),
                empty_receiver{bufs}));
            state->initiate(); // will reap completions if no buffers free
            state.release();
        }
        testio.wait_until_done();
    }

    struct sqe_exhaustion_does_not_reorder_writes_receiver
    {
        static constexpr size_t COUNT = 128;

        uint32_t &offset;
        std::vector<monad::async::file_offset_t> &seq;

        inline void set_value(
            monad::async::erased_connected_operation *io_state,
            monad::async::write_single_buffer_sender::result_type r);
    };

    using sqe_exhaustion_does_not_reorder_writes_state_unique_ptr_type =
        monad::async::AsyncIO::connected_operation_unique_ptr_type<
            monad::async::write_single_buffer_sender,
            sqe_exhaustion_does_not_reorder_writes_receiver>;

    inline void sqe_exhaustion_does_not_reorder_writes_receiver::set_value(
        monad::async::erased_connected_operation *io_state,
        monad::async::write_single_buffer_sender::result_type r)
    {
        MONAD_ASSERT(r);
        auto *state = static_cast<
            sqe_exhaustion_does_not_reorder_writes_state_unique_ptr_type::
                element_type *>(io_state);
        seq.push_back(state->sender().offset().offset);
        if (seq.size() < COUNT) {
            auto s1 = state->executor()->make_connected(
                monad::async::write_single_buffer_sender(
                    {0, offset}, monad::async::DISK_PAGE_SIZE),
                sqe_exhaustion_does_not_reorder_writes_receiver{offset, seq});
            offset += monad::async::DISK_PAGE_SIZE;
            s1->sender().advance_buffer_append(monad::async::DISK_PAGE_SIZE);
            s1->initiate();
            s1.release();
            auto s2 = state->executor()->make_connected(
                monad::async::write_single_buffer_sender(
                    {0, offset}, monad::async::DISK_PAGE_SIZE),
                sqe_exhaustion_does_not_reorder_writes_receiver{offset, seq});
            offset += monad::async::DISK_PAGE_SIZE;
            s2->sender().advance_buffer_append(monad::async::DISK_PAGE_SIZE);
            s2->initiate();
            s2.release();
        }
    }

    TEST(AsyncIO, sqe_exhaustion_does_not_reorder_writes)
    {
        monad::async::storage_pool pool(
            monad::async::use_anonymous_inode_tag{});
        monad::io::Ring testring1(4);
        monad::io::Ring testring2(
            {sqe_exhaustion_does_not_reorder_writes_receiver::COUNT,
             false,
             std::nullopt});
        monad::io::Buffers testrwbuf =
            monad::io::make_buffers_for_segregated_read_write(
                testring1,
                testring2,
                1,
                sqe_exhaustion_does_not_reorder_writes_receiver::COUNT,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        monad::async::AsyncIO testio(pool, testrwbuf);
        {
            auto const [max_sq_entries, max_cq_entries] =
                testio.io_uring_ring_entries_left(false);
            std::cout << "   non-write ring: sq entries created = "
                      << max_sq_entries
                      << " cq entries created = " << max_cq_entries
                      << std::endl;
        }
        {
            auto const [max_sq_entries, max_cq_entries] =
                testio.io_uring_ring_entries_left(true);
            std::cout << "       write ring: sq entries created = "
                      << max_sq_entries
                      << " cq entries created = " << max_cq_entries
                      << std::endl;
        }
        std::vector<monad::async::file_offset_t> seq;
        seq.reserve(sqe_exhaustion_does_not_reorder_writes_receiver::COUNT * 2);

        uint32_t offset = 0;
        auto s1 = testio.make_connected(
            monad::async::write_single_buffer_sender(
                {0, offset}, monad::async::DISK_PAGE_SIZE),
            sqe_exhaustion_does_not_reorder_writes_receiver{offset, seq});
        offset += monad::async::DISK_PAGE_SIZE;
        s1->sender().advance_buffer_append(monad::async::DISK_PAGE_SIZE);
        s1->initiate();
        s1.release();
        testio.wait_until_done();
        std::cout << "   " << seq.size() << " offsets written." << std::endl;

        uint32_t offset2 = 0;
        for (auto &i : seq) {
            EXPECT_EQ(i, offset2);
            offset2 += monad::async::DISK_PAGE_SIZE;
        }
        EXPECT_EQ(seq.back(), offset - monad::async::DISK_PAGE_SIZE);
    }
}
