// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include "fuzz/one_hundred_updates.hpp"

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/hex_literal.hpp>
#include <category/mpt/detail/boost_fiber_workarounds.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

#include <chrono>
#include <utility>
#include <vector>

namespace
{
    using namespace monad::test;
    using namespace MONAD_ASYNC_NAMESPACE;

    void find(
        UpdateAuxImpl *aux, inflight_map_t *const inflights,
        NodeCursor const root, monad::byte_string_view const prefix,
        monad::byte_string_view const key, monad::byte_string_view const value)
    {
        monad::threadsafe_boost_fibers_promise<
            monad::mpt::find_cursor_result_type>
            promise;
        find_notify_fiber_future(*aux, *inflights, promise, root, prefix);
        auto const [it, errc] = promise.get_future().get();
        ASSERT_TRUE(it.is_valid());
        EXPECT_EQ(errc, monad::mpt::find_result::success);
        EXPECT_EQ(it.node->value(), monad::byte_string{});
        EXPECT_EQ(
            it.node->data(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);
        EXPECT_EQ(it.machine->get_depth(), NibblesView{prefix}.nibble_size());

        monad::threadsafe_boost_fibers_promise<
            monad::mpt::find_cursor_result_type>
            promise2;
        find_notify_fiber_future(*aux, *inflights, promise2, it, key);
        auto const [it2, errc2] = promise2.get_future().get();
        ASSERT_TRUE(it2.is_valid());
        EXPECT_EQ(errc2, monad::mpt::find_result::success);
        EXPECT_EQ(it2.node->value(), value);
        EXPECT_EQ(
            it2.machine->get_depth(),
            NibblesView{prefix}.nibble_size() + NibblesView{key}.nibble_size());
    };

    void poll(AsyncIO *const io, bool *signal_done)
    {
        while (!*signal_done) {
            io->poll_nonblocking(1);
            boost::this_fiber::sleep_for(std::chrono::milliseconds(1));
        }
    };

    struct OnDiskMerkleTriePreInsert : public OnDiskMerkleTrieGTest
    {
        monad::byte_string const prefix = 0x00_hex;

        void batch_upsert_with_prefix()
        {
            std::vector<Update> updates_alloc;
            updates_alloc.reserve(one_hundred_updates.size());
            UpdateList ul;
            for (auto const &i : one_hundred_updates) {
                ul.push_front(
                    updates_alloc.emplace_back(make_update(i.first, i.second)));
            }
            this->root = upsert_updates(
                this->aux,
                *this->sm,
                std::move(this->root),
                0,
                make_update(prefix, {}, false, std::move(ul)));
        }
    };

    TEST_F(OnDiskMerkleTriePreInsert, single_thread_one_find_fiber)
    {
        this->sm =
            std::make_unique<StateMachineMerkleWithPrefix<2>>(Nibbles{prefix});
        batch_upsert_with_prefix();

        inflight_map_t inflights;

        boost::fibers::fiber find_fiber(
            find,
            &this->aux,
            &inflights,
            NodeCursor{this->sm->clone(), *root.get()},
            prefix,
            one_hundred_updates[0].first,
            one_hundred_updates[0].second);
        bool signal_done = false;
        boost::fibers::fiber poll_fiber(poll, aux.io, &signal_done);
        find_fiber.join();
        signal_done = true;
        poll_fiber.join();
    }

    TEST_F(OnDiskMerkleTriePreInsert, single_thread_one_hundred_find_fibers)
    {
        this->sm =
            std::make_unique<StateMachineMerkleWithPrefix<2>>(Nibbles{prefix});
        batch_upsert_with_prefix();

        inflight_map_t inflights;
        std::vector<boost::fibers::fiber> fibers;
        for (auto const &[key, val] : one_hundred_updates) {
            fibers.emplace_back(
                find,
                &this->aux,
                &inflights,
                NodeCursor{this->sm->clone(), *root.get()},
                prefix,
                key,
                val);
        }

        bool signal_done = false;
        boost::fibers::fiber poll_fiber(poll, aux.io, &signal_done);

        for (auto &fiber : fibers) {
            fiber.join();
        }
        signal_done = true;
        poll_fiber.join();
    }
}
