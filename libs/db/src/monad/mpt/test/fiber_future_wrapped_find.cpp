#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include "fuzz/one_hundred_updates.hpp"

#include <monad/async/config.hpp>
#include <monad/async/io.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_util.h>
#include <monad/fiber/future.hpp>
#include <monad/fiber/run_queue.h>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <bit>
#include <cstddef>
#include <cstdint>
#include <chrono>
#include <deque>
#include <utility>
#include <vector>

namespace
{
    using namespace monad::test;
    using namespace MONAD_ASYNC_NAMESPACE;

    constexpr std::size_t TEST_STACK_SIZE = 1 << 17; // 128 KiB

    struct FindArgs
    {
        UpdateAuxImpl *aux;
        inflight_map_t *const inflights;
        Node *const root;
        monad::byte_string_view const key;
        monad::byte_string_view const value;
    };

    std::uintptr_t find(std::uintptr_t arg0)
    {
        auto *const find_args = std::bit_cast<FindArgs*>(arg0);
        monad::fiber::simple_promise<find_result_type> promise;
        fiber_find_request_t const request{
            .promise = &promise, .start = NodeCursor{*find_args->root},
            .key = find_args->key};
        find_notify_fiber_future(*find_args->aux, *find_args->inflights, request);
        auto const [it, errc] = request.promise->get_future().get();
        if (!it.is_valid())
            return 1;
        EXPECT_EQ(errc, monad::mpt::find_result::success);
        EXPECT_EQ(it.node->value(), find_args->value);
        return 0;
    }

    void init_find_fiber(monad_fiber_t *fiber, monad_fiber_prio_t prio,
        FindArgs *find_args)
    {
        monad_fiber_stack_t stack;
        std::size_t stack_size = TEST_STACK_SIZE;
        ASSERT_EQ(monad_fiber_alloc_stack(&stack_size, &stack), 0);
        monad_fiber_init(fiber, stack);
        ASSERT_EQ(monad_fiber_set_function(fiber, prio, find,
            std::bit_cast<uintptr_t>(find_args)), 0);
    }

    TEST_F(OnDiskMerkleTrieGTest, single_thread_one_find_fiber)
    {
        std::vector<Update> updates;
        for (auto const &i : one_hundred_updates) {
            updates.emplace_back(make_update(i.first, i.second));
        }
        this->root = upsert_vector(
            this->aux, *this->sm, std::move(this->root), std::move(updates));
        EXPECT_EQ(
            root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);

        inflight_map_t inflights;
        FindArgs find_args = {
            &this->aux,
            &inflights,
            root.get(),
            one_hundred_updates[0].first,
            one_hundred_updates[0].second
        };

        monad_fiber_t fiber;
        monad_fiber_suspend_info_t suspend_info;
        init_find_fiber(&fiber, MONAD_FIBER_PRIO_HIGHEST, &find_args);

        while (true) {
            const int rc = monad_fiber_run(&fiber, &suspend_info);
            ASSERT_EQ(rc, 0);
            if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
                ASSERT_EQ(suspend_info.eval, 0);
                break;
            }
            do {
                aux.io->poll_nonblocking(1);
                std::this_thread::sleep_for(std::chrono::milliseconds(1));
            } while (!monad_fiber_is_runnable(&fiber));
        }
    }

    TEST_F(OnDiskMerkleTrieGTest, single_thread_one_hundred_find_fibers)
    {
        std::vector<Update> updates;
        for (auto const &i : one_hundred_updates) {
            updates.emplace_back(make_update(i.first, i.second));
        }
        this->root = upsert_vector(
            this->aux, *this->sm, std::move(this->root), std::move(updates));
        EXPECT_EQ(
            root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);

        inflight_map_t inflights;
        std::deque<monad_fiber_t> fibers;
        std::deque<FindArgs> fiber_func_args;
        monad_run_queue_t *run_queue;

        ASSERT_EQ(monad_run_queue_create(size(one_hundred_updates), &run_queue), 0);
        for (std::size_t i = 0; auto const &[key, val] : one_hundred_updates) {
            FindArgs& find_args = fiber_func_args.emplace_back(
                &this->aux, &inflights, root.get(), key, val);
            monad_fiber_t& fiber = fibers.emplace_back();
            init_find_fiber(&fiber, MONAD_FIBER_PRIO_HIGHEST + i++, &find_args);
            ASSERT_EQ(monad_run_queue_try_push(run_queue, &fiber), 0);
        }

        std::size_t fibers_done = 0;
        while (fibers_done < size(one_hundred_updates)) {
            monad_fiber_suspend_info_t suspend_info;
            monad_fiber_t *next_fiber = monad_run_queue_try_pop(run_queue);

            while (next_fiber == nullptr) {
                // When there's nothing to do, I/O poll until at least one fiber
                // is scheduled to run again
                aux.io->poll_nonblocking(1);
                std::this_thread::sleep_for(std::chrono::milliseconds(1));
                next_fiber = monad_run_queue_try_pop(run_queue);
            }

            const int rc = monad_fiber_run(next_fiber, &suspend_info);
            ASSERT_EQ(rc, 0);
            if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
                ASSERT_EQ(suspend_info.eval, 0);
                ++fibers_done;
            }
        }

        ASSERT_TRUE(monad_run_queue_is_empty(run_queue));
        for (monad_fiber_t &fiber : fibers)
            monad_fiber_free_stack(fiber.stack);
        monad_run_queue_destroy(run_queue);
    }
}
