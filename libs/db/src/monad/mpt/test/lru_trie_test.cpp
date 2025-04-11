#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp" // NOLINT

#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>

using namespace monad::mpt;
using namespace monad::literals;
using namespace monad::test;

TEST(NodeCache, works)
{
    NodeCache node_cache(3 * NodeCache::AVERAGE_NODE_SIZE);
    NodeCache::ConstAccessor acc;
    auto make_node = [&](uint32_t v) {
        monad::byte_string value(84, 0);
        memcpy(value.data(), &v, 4);
        auto node = monad::mpt::make_node(0, {}, {}, std::move(value), 0, 0);
        MONAD_ASSERT(node->get_mem_size() == 100);
        return node;
    };
    auto get_acc_value = [&] -> uint32_t {
        auto const view(acc->second->val->value());
        MONAD_ASSERT(84 == view.size());
        return *(uint32_t const *)view.data();
    };
    node_cache.insert(chunk_offset_t(1, 0), make_node(0x123));
    node_cache.insert(chunk_offset_t(2, 0), make_node(0xdead));
    node_cache.insert(chunk_offset_t(3, 0), make_node(0xbeef));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(3, 0)));
    EXPECT_EQ(get_acc_value(), 0xbeef);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(2, 0)));
    EXPECT_EQ(get_acc_value(), 0xdead);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(1, 0)));
    EXPECT_EQ(get_acc_value(), 0x123);

    node_cache.insert(chunk_offset_t(4, 0), make_node(0xcafe));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(2, 0)));
    EXPECT_EQ(get_acc_value(), 0xdead);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(1, 0)));
    EXPECT_EQ(get_acc_value(), 0x123);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(4, 0)));
    EXPECT_EQ(get_acc_value(), 0xcafe);

    node_cache.insert(chunk_offset_t(2, 0), make_node(0xc0ffee));
    node_cache.insert(chunk_offset_t(5, 0), make_node(100));
    EXPECT_EQ(node_cache.size(), 3);

    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(2, 0)));
    EXPECT_EQ(get_acc_value(), 0xc0ffee);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(4, 0)));
    EXPECT_EQ(get_acc_value(), 0xcafe);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(5, 0)));
    EXPECT_EQ(get_acc_value(), 100);

    monad::byte_string value(84 * 3, 0);
    memcpy(value.data(), "hihi", 4);
    auto node = monad::mpt::make_node(0, {}, {}, std::move(value), 0, 0);
    node_cache.insert(chunk_offset_t(6, 0), std::move(node));
    // Everything else should get evicted
    EXPECT_EQ(node_cache.size(), 1);
    ASSERT_TRUE(node_cache.find(acc, chunk_offset_t(6, 0)));
    auto const view(acc->second->val->value());
    EXPECT_EQ(0, memcmp(view.data(), "hihi", 4));
}

struct LRUTrieTest : public OnDiskTrieGTest
{
};

TEST_F(LRUTrieTest, lru_large_values)
{
    constexpr uint64_t version = 0;
    // make sure leaves are not cached
    auto const key1 = 0x0000112_hex;
    auto const key2 = 0x0000123_hex;
    auto const value1 = monad::byte_string(100 * 1024 * 1024, 0xf); // 100 MB
    auto const value2 = monad::byte_string(255 * 1024 * 1024, 0x3); // 255 MB

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(key1, value1),
        make_update(key2, value2));
    {
        auto [leaf_it, res] =
            find_blocking(this->aux, *this->root, key1, version);
        auto *leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value1);
    }
    {
        auto [leaf_it, res] =
            find_blocking(this->aux, *this->root, key2, version);
        auto *leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value2);
    }

    NodeCache node_cache(256 * 1024 * 1024);
    inflight_map_owning_t inflights;
    {
        monad::threadsafe_boost_fibers_promise<find_owning_cursor_result_type>
            p;
        auto fut = p.get_future();
        auto wait_until_done = monad::make_scope_exit(
            [&]() noexcept { this->aux.io->wait_until_done(); });
        load_root_notify_fiber_future(
            this->aux, node_cache, inflights, p, version);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            this->aux.io->wait_until_done();
        }
        OwningNodeCursor cur = fut.get().first;
        std::cout << "After load of root 1, node cache contains "
                  << node_cache.size() << " items occupying "
                  << node_cache.memory() << " bytes." << std::endl;
        p = {};
        fut = p.get_future();
        find_owning_notify_fiber_future(
            this->aux, node_cache, inflights, p, cur, key1, version);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            this->aux.io->wait_until_done();
        }
        auto [leaf_it, res] = fut.get();
        auto &leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value1);
        std::cout << "After load of 100 Mb value, node cache contains "
                  << node_cache.size() << " items occupying "
                  << node_cache.memory() << " bytes." << std::endl;
        // There should be the 100Mb value, and its root
        EXPECT_EQ(node_cache.size(), 2);
    }

    {
        monad::threadsafe_boost_fibers_promise<find_owning_cursor_result_type>
            p;
        auto fut = p.get_future();
        auto wait_until_done = monad::make_scope_exit(
            [&]() noexcept { this->aux.io->wait_until_done(); });
        load_root_notify_fiber_future(
            this->aux, node_cache, inflights, p, version);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            this->aux.io->wait_until_done();
        }
        OwningNodeCursor cur = fut.get().first;
        std::cout << "After load of root 2, node cache contains "
                  << node_cache.size() << " items occupying "
                  << node_cache.memory() << " bytes." << std::endl;
        // Same root should be found from cache
        EXPECT_EQ(node_cache.size(), 2);
        p = {};
        fut = p.get_future();
        find_owning_notify_fiber_future(
            this->aux, node_cache, inflights, p, cur, key2, version);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            this->aux.io->wait_until_done();
        }
        auto [leaf_it, res] = fut.get();
        auto &leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value2);
        // Max cache mem size of 256Mb should mean loading this evicts the 100Mb
        // value as it should be the least recently used item
        std::cout << "After load of 255 Mb value, node cache contains "
                  << node_cache.size() << " items occupying "
                  << node_cache.memory() << " bytes." << std::endl;
        EXPECT_EQ(node_cache.size(), 2);
    }
}
