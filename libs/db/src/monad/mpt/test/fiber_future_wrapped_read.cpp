#include "test_fixtures_gtest.hpp" // NOLINT

#include <monad/async/boost_fiber_wrappers.hpp>
#include <monad/async/concepts.hpp>
#include <monad/async/config.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/util.hpp>
#include <monad/core/small_prng.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/fiber/future/async.hpp>
#include <boost/fiber/future/future.hpp>
#include <boost/fiber/future/future_status.hpp>
#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <chrono>
#include <cstddef>
#include <cstring>
#include <iostream>
#include <ostream>
#include <utility>
#include <vector>

using namespace MONAD_ASYNC_NAMESPACE;

struct FiberFutureWrappedFind
    : public monad::test::AsyncTestFixture<::testing::Test>
{
};

TEST_F(FiberFutureWrappedFind, single_thread_fibers_read)
{
    struct receiver_t
    {
        FiberFutureWrappedFind::shared_state_t *const fixture_shared_state;
        ::monad::fiber::promise<
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type>
            promise;
        chunk_offset_t offset;

        enum : bool
        {
            lifetime_managed_internally = false // we manage state lifetime
        };

        bool done{false};

        receiver_t(
            FiberFutureWrappedFind::shared_state_t *fixture_shared_state_,
            ::monad::fiber::promise<
                MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type>
                &&p,
            chunk_offset_t const offset_)
            : fixture_shared_state(fixture_shared_state_)
            , promise(std::move(p))
            , offset(offset_)
        {
        }

        void set_value(
            erased_connected_operation *,
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type res)
        {
            ASSERT_TRUE(res);
            auto &buffer = res.assume_value().get();

            EXPECT_EQ(
                buffer.front(),
                fixture_shared_state->testfilecontents[offset.offset]);

            promise.set_value(std::move(buffer));
            done = true;
        }
    };

    // Two diff implementations,
    // impl_sender: request read thru an io sender
    auto impl_sender = [&]() -> result<std::vector<std::byte>> {
        // This initiates the i/o reading DISK_PAGE_SIZE bytes from a
        // randomized offset
        using promise_result_t =
            MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::buffer_type;

        chunk_offset_t const offset(
            0,
            round_down_align<DISK_PAGE_BITS>(
                shared_state_()->test_rand() %
                (TEST_FILE_SIZE - DISK_PAGE_SIZE)));
        auto sender = read_single_buffer_sender(offset, DISK_PAGE_SIZE);
        ::monad::fiber::promise<promise_result_t> promise;
        auto fut = promise.get_future();
        auto iostate = shared_state_()->testio->make_connected(
            std::move(sender),
            receiver_t{shared_state_().get(), std::move(promise), offset});
        iostate->initiate();
        std::cout << "sender..." << std::endl;

        auto bytesread = fut.get();
        // Return a copy of the registered buffer with lifetime held by fut
        return std::vector<std::byte>(bytesread.begin(), bytesread.end());
    };
    // impl_fiber_wrapper_sender: request read thru fiber wrapped io sender
    auto impl_fiber_wrapper_sender = []() -> result<std::vector<std::byte>> {
        // This initiates the i/o reading DISK_PAGE_SIZE bytes from offset
        // 0, returning a boost fiber future like object
        auto fut = boost_fibers::read_single_buffer(
            *shared_state_()->testio, chunk_offset_t{0, 0}, DISK_PAGE_SIZE);
        std::cout << "fiber wrapped sender..." << std::endl;
        // You can do other stuff here, like initiate more i/o or do compute

        // When you really do need the result to progress further, suspend
        // execution until the i/o completes. The TRY operation will
        // propagate any failures out the return type of this lambda, if the
        // operation was successful `res` get the result.
        BOOST_OUTCOME_TRY(auto bytesread_, fut.get());
        auto &bytesread = bytesread_.get();

        EXPECT_EQ(DISK_PAGE_SIZE, bytesread.size());
        EXPECT_EQ(
            0,
            memcmp(
                bytesread.data(),
                shared_state_()->testfilecontents.data(),
                DISK_PAGE_SIZE));
        // Return a copy of the registered buffer with lifetime held by fut
        return std::vector<std::byte>(bytesread.begin(), bytesread.end());
    };

    // Launch the fiber task
    std::vector<::monad::fiber::future<result<std::vector<std::byte>>>>
        futures;
    int const n_each = MAX_CONCURRENCY / 2;
    futures.reserve(MAX_CONCURRENCY);
    for (int i = 0; i < n_each; ++i) {
        futures.emplace_back(::monad::fiber::async(impl_sender));
        futures.emplace_back(::monad::fiber::async(impl_fiber_wrapper_sender));
    }

    // Pump the loop until the fiber completes
    for (auto &fut : futures) {
        while (!fut.ready()) {
            shared_state_()->testio->poll_nonblocking(1);
        }
        auto res = fut.get();
    }
}
