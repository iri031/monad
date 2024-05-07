#include "gtest/gtest.h"

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <algorithm>
#include <cstdint>
#include <iterator>
#include <list>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

using namespace ::monad::test;

template <typename TFixture>
struct TrieTest : public TFixture
{
};

using TrieTypes =
    ::testing::Types<InMemoryMerkleTrieGTest, OnDiskMerkleTrieGTest>;
TYPED_TEST_SUITE(TrieTest, TrieTypes);

template <typename TFixture>
struct EraseTrieTest : public TFixture
{
};

using EraseTrieType = ::testing::Types<
    EraseFixture<InMemoryMerkleTrieGTest>, EraseFixture<OnDiskMerkleTrieGTest>>;
TYPED_TEST_SUITE(EraseTrieTest, EraseTrieType);

TYPED_TEST(TrieTest, nested_leave_one_child_on_branch_with_leaf)
{
    auto const key1 = 0x123456_hex;
    auto const subkey2 = 0x1234_hex;
    auto const subkey3 = 0x2345_hex;
    auto const value = 0xdeadbeef_hex;

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(key1, value),
        make_update(key1 + subkey2, value),
        make_update(key1 + subkey3, value));

    UpdateList next;
    Update sub1{
        .key = subkey2,
        .value = std::nullopt,
        .incarnation = false,
        .next = UpdateList{}};
    next.push_front(sub1);
    Update base{
        .key = key1,
        .value = value,
        .incarnation = false,
        .next = std::move(next)};
    UpdateList updates;
    updates.push_front(base);

    this->root =
        upsert(this->aux, *this->sm, std::move(this->root), std::move(updates));
    EXPECT_EQ(
        this->root_hash(),
        0xeefbd82ec11d1d2d83a23d661a8eece950f1e29fa72665f07b57fc9a903257cc_hex);
}

// Test Starts
TYPED_TEST(TrieTest, insert_one_element)
{
    // keys are the same
    auto const key =
        0x1234567812345678123456781234567812345678123456781234567812345678_hex;
    auto const val1 =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex;
    auto const val2 =
        0xdeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddead_hex;

    // single update
    this->root =
        upsert_updates(this->aux, *this->sm, {}, make_update(key, val1));
    EXPECT_EQ(
        this->root_hash(),
        0xa1aa368afa323866e03c21927db548afda3da793f4d3c646d7dd8109477b907e_hex);

    // update again
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_update(key, val2));
    EXPECT_EQ(
        this->root_hash(),
        0x5d225e3b0f1f386171899d343211850f102fa15de6e808c6f614915333a4f3ab_hex);
}

TYPED_TEST(TrieTest, simple_inserts)
{
    auto const &kv = fixed_updates::kv;

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));
    EXPECT_EQ(
        this->root_hash(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(
        this->root_hash(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}

TYPED_TEST(TrieTest, upsert_fixed_key_length)
{
    auto const &kv = var_len_values::kv;
    // insert kv 0,1
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));
    EXPECT_EQ(
        this->root_hash(),
        0xb28f388f1d98e9f2fc9daa80988cb324e0d517a86fb1f46b0bf8670728143001_hex);

    // insert kv 2,3
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(
        this->root_hash(),
        0x30175d933b55cc3528abc7083210296967ea3ccb2afeb12d966a7789e8d0fc1f_hex);

    // insert kv 4,5,6
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[4].first, kv[4].second),
        make_update(kv[5].first, kv[5].second),
        make_update(kv[6].first, kv[6].second));
    EXPECT_EQ(
        this->root_hash(),
        0x399580bb7585999a086e9bc6f29af647019826b49ef9d84004b0b03323ddb212_hex);

    // erases
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[4].first));
    EXPECT_EQ(
        this->root_hash(),
        0x3467f96b8c7a1f9646cbee98500111b37d160ec0f02844b2bdcb89c8bcd3878a_hex);

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[6].first));
    EXPECT_EQ(
        this->root_hash(),
        0xdba3fae4737cde5014f6200508d7659ccc146b760e3a2ded47d7c422372b6b6c_hex);

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_erase(kv[2].first),
        make_erase(kv[3].first),
        make_erase(kv[5].first));
    EXPECT_EQ(
        this->root_hash(),
        0xb28f388f1d98e9f2fc9daa80988cb324e0d517a86fb1f46b0bf8670728143001_hex);

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[1].first));
    EXPECT_EQ(
        this->root_hash(),
        0x065ed1753a679bbde2ce3ba5af420292b86acd3fdc2ad74215d54cc10b2add72_hex);

    // erase the last one
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[0].first));
    EXPECT_EQ(this->root, nullptr);
}

TYPED_TEST(TrieTest, insert_unrelated_leaves_then_read)
{
    auto const &kv = unrelated_leaves::kv;

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));
    EXPECT_EQ(
        this->root_hash(),
        0xc2cbdf038f464a595ac12a257d48cc2a36614f0adfd2e9a08b79c5b34b52316a_hex);

    // two other updates for next batch
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(
        this->root_hash(),
        0xd339cf4033aca65996859d35da4612b642664cc40734dbdd40738aa47f1e3e44_hex);

    {
        auto [leaf_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, kv[0].first);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{kv[0].first}.nibble_size());
        EXPECT_EQ(
            (monad::byte_string_view{
                leaf_it.node->value_data(), leaf_it.node->value_len}),
            kv[0].second);
    }
    {
        auto [leaf_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, kv[1].first);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{kv[1].first}.nibble_size());
        EXPECT_EQ(
            (monad::byte_string_view{
                leaf_it.node->value_data(), leaf_it.node->value_len}),
            kv[1].second);
    }
    {
        auto [leaf_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, kv[2].first);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{kv[2].first}.nibble_size());
        EXPECT_EQ(
            (monad::byte_string_view{
                leaf_it.node->value_data(), leaf_it.node->value_len}),
            kv[2].second);
    }
    {
        auto [leaf_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, kv[3].first);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{kv[3].first}.nibble_size());
        EXPECT_EQ(
            (monad::byte_string_view{
                leaf_it.node->value_data(), leaf_it.node->value_len}),
            kv[3].second);
    }
}

TYPED_TEST(TrieTest, inserts_shorter_leaf_data)
{
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0x1234567812345678123456781234567812345678123456781234567812345678_hex,
         0xdeadbeef_hex},
        {0x1234567822345678123456781234567812345678123456781234567812345678_hex,
         0xdeadbeefcafebabe_hex},
        {0x1234567832345678123456781234567812345678123456781234567812345671_hex,
         0xdeadcafe_hex},
        {0x1234567832345678123456781234567812345678123456781234567812345678_hex,
         0xdead_hex}};

    std::vector<Update> update_vec;
    std::ranges::transform(
        kv, std::back_inserter(update_vec), [](auto &su) -> Update {
            auto &[k, v] = su;
            return make_update(k, monad::byte_string_view{v});
        });
    this->root = upsert_vector(this->aux, *this->sm, {}, std::move(update_vec));
    EXPECT_EQ(
        this->root_hash(),
        0xb796133251968233b84f3fcf8af88cdb42eeabe793f27835c10e8b46c91dfa4a_hex);
}

TYPED_TEST(TrieTest, empty_trie_with_empty_update)
{
    // no update
    this->root = upsert_updates(this->aux, *this->sm, std::move(this->root));
    EXPECT_EQ(
        this->root_hash(),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_hex);
}

////////////////////////////////////////////////////////////////////
// Erase Trie Tests
////////////////////////////////////////////////////////////////////

TYPED_TEST(EraseTrieTest, none)
{
    EXPECT_EQ(
        this->root_hash(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}

TYPED_TEST(EraseTrieTest, empty_update_list)
{
    // no update
    this->root = upsert_updates(this->aux, *this->sm, std::move(this->root));
    EXPECT_EQ(
        this->root_hash(),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}

TYPED_TEST(EraseTrieTest, remove_everything)
{
    auto kv = fixed_updates::kv;

    std::vector<Update> update_vec;
    std::ranges::transform(
        kv, std::back_inserter(update_vec), [](auto &su) -> Update {
            auto &[k, v] = su;
            return make_erase(k);
        });
    this->root = upsert_vector(
        this->aux, *this->sm, std::move(this->root), std::move(update_vec));
    EXPECT_EQ(
        this->root_hash(),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_hex);
}

TYPED_TEST(EraseTrieTest, delete_single_branch)
{
    auto kv = fixed_updates::kv;

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_erase(kv[2].first),
        make_erase(kv[3].first));
    EXPECT_EQ(
        this->root_hash(),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
}

TYPED_TEST(EraseTrieTest, delete_one_at_a_time)
{
    auto kv = fixed_updates::kv;

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[2].first));
    EXPECT_EQ(
        this->root_hash(),
        0xd8b34a85db25148b1901459eac9805edadaa20b03f41fecd3b571f3b549e2774_hex);

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[1].first));
    EXPECT_EQ(
        this->root_hash(),
        0x107c8dd7bf9e7ca1faaa2c5856b412a8d7fccfa0005ca2500673a86b9c1760de_hex);

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[0].first));
    EXPECT_EQ(
        this->root_hash(),
        0x15fa9c02a40994d2d4f9c9b21daba3c4e455985490de5f9ae4889548f34d5873_hex);

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[3].first));
    EXPECT_EQ(
        this->root_hash(),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_hex);
}

TYPED_TEST(TrieTest, upsert_var_len_keys)
{
    // 2 accounts, kv[0] and kv[1]
    // kv[2,3,4] are of kv[0]'s storages
    // kv[5,6,7] are of kv[1]'s storages
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0x0a0b_hex}, // 0
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbcc_hex,
         0x1234_hex}, // 1
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbddaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0xbeef_hex}, // 2
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbddabcdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xdeadbeef_hex}, // 3
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbddabcdeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xcafe_hex}, // 4
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0xbeef_hex}, // 5
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbccabcdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xdeadbeef_hex}, // 6
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbccabcdeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xcafe_hex}}; // 7

    // insert kv 0,1
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second),
        make_update(kv[2].first, kv[2].second));
    EXPECT_EQ(
        this->root_hash(),
        0xd02534184b896dd4cb37fb34f176cafb508aa2ebc19a773c332514ca8c65ca10_hex);

    // update first trie's account value
    auto acc1 =
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex;
    auto new_val = 0x1234_hex;
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(acc1, new_val));
    EXPECT_EQ(
        this->root_hash(),
        0xe9e9d8bd0c74fe45b27ac36169fd6d58a0ee4eb6573fdf6a8680be814a63d2f5_hex);

    // update storages
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(
        this->root_hash(),
        0xc2f4c0bf52f5b277252ecfe9df3c38b44d1787b3f89febde1d29406eb06e8f93_hex);

    // update storages again
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[4].first, kv[4].second));
    EXPECT_EQ(
        this->root_hash(),
        0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);

    // erase storage kv 3, 4
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_erase(kv[3].first),
        make_erase(kv[4].first));
    EXPECT_EQ(
        this->root_hash(),
        0xe9e9d8bd0c74fe45b27ac36169fd6d58a0ee4eb6573fdf6a8680be814a63d2f5_hex);

    // incarnation: now acc(kv[0]) only has 1 storage
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, new_val, true),
        make_update(kv[4].first, kv[4].second));
    EXPECT_EQ(
        this->root_hash(),
        0x2667b2bcc7c6a9afcd5a621be863fc06bf76022450e7e2e11ef792d63c7a689c_hex);

    // insert storages to the second account
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[5].first, kv[5].second),
        make_update(kv[6].first, kv[6].second),
        make_update(kv[7].first, kv[7].second));
    EXPECT_EQ(
        this->root_hash(),
        0x7954fcaa023fb356d6c626119220461c7859b93abd6ea71eac342d8407d7051e_hex);

    // erase all storages of kv[0].
    // TEMPORARY Note: when an existing account has no storages, the computed
    // leaf data is the input value, we don't concatenate with `empty_trie_hash`
    // in this poc impl yet.
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[4].first));
    EXPECT_EQ(
        this->root_hash(),
        0x055a9738d15fb121afe470905ca2254da172da7a188d8caa690f279c10422380_hex);

    // erase whole first account (kv[0])
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_erase(kv[0].first),
        make_update(kv[3].first, kv[3].second), /*the following are ignored*/
        make_update(kv[4].first, kv[4].second));
    EXPECT_EQ(
        this->root_hash(),
        0x2c077fecb021212686442677ecd59ac2946c34e398b723cf1be431239cb11858_hex);
}

TYPED_TEST(TrieTest, upsert_var_len_keys_nested)
{
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0x0a0b_hex},
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbcc_hex,
         0x1234_hex}};
    std::vector<std::pair<monad::byte_string, monad::byte_string>> storage_kv{
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0xbeef_hex},
        {0xabcdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xdeadbeef_hex},
        {0xabcdeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xcafe_hex}};

    Update a = make_update(storage_kv[0].first, storage_kv[0].second);
    UpdateList storage;
    storage.push_front(a);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(kv[0].first, kv[0].second, false, std::move(storage)),
        make_update(kv[1].first, kv[1].second));
    EXPECT_EQ(
        this->root_hash(),
        0xd02534184b896dd4cb37fb34f176cafb508aa2ebc19a773c332514ca8c65ca10_hex);

    // update first trie mid leaf data
    // with nested storage changes but doesn't change any value
    auto acc1 = kv[0].first;
    auto new_val = 0x1234_hex;
    storage.clear(); // NOLINT
    storage.push_front(a);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(acc1, new_val, false, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0xe9e9d8bd0c74fe45b27ac36169fd6d58a0ee4eb6573fdf6a8680be814a63d2f5_hex);

    // update storages
    Update b = make_update(storage_kv[1].first, storage_kv[1].second);
    storage.clear(); // NOLINT
    storage.push_front(b);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0xc2f4c0bf52f5b277252ecfe9df3c38b44d1787b3f89febde1d29406eb06e8f93_hex);

    // update storage again
    Update c = make_update(storage_kv[2].first, storage_kv[2].second);
    storage.clear(); // NOLINT
    storage.push_front(c);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);

    // erase some storage
    storage.clear(); // NOLINT
    Update erase_b = make_erase(storage_kv[1].first);
    Update erase_c = make_erase(storage_kv[2].first);
    storage.push_front(erase_b);
    storage.push_front(erase_c);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0xe9e9d8bd0c74fe45b27ac36169fd6d58a0ee4eb6573fdf6a8680be814a63d2f5_hex);

    // incarnation
    storage.clear(); // NOLINT
    storage.push_front(c);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, new_val, true, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0x2667b2bcc7c6a9afcd5a621be863fc06bf76022450e7e2e11ef792d63c7a689c_hex);

    // insert storages to the second account
    storage.clear(); // NOLINT
    storage.push_front(a);
    storage.push_front(b);
    storage.push_front(c);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[1].first, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0x7954fcaa023fb356d6c626119220461c7859b93abd6ea71eac342d8407d7051e_hex);

    // erase all storages of kv[0].
    storage.clear(); // NOLINT
    storage.push_front(erase_c);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, std::move(storage)));
    EXPECT_EQ(
        this->root_hash(),
        0x055a9738d15fb121afe470905ca2254da172da7a188d8caa690f279c10422380_hex);

    // erase whole first account (kv[0])
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[0].first));
    EXPECT_EQ(
        this->root_hash(),
        0x2c077fecb021212686442677ecd59ac2946c34e398b723cf1be431239cb11858_hex);
}

TYPED_TEST(TrieTest, nested_updates_block_no)
{
    this->sm = std::make_unique<StateMachineWithBlockNo>();

    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0x1234_hex},
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbcc_hex,
         0x1234_hex}};
    std::vector<std::pair<monad::byte_string, monad::byte_string>> storage_kv{
        {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbdd_hex,
         0xbeef_hex},
        {0xabcdaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xdeadbeef_hex},
        {0xabcdeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_hex,
         0xcafe_hex}};

    Update a = make_update(storage_kv[0].first, storage_kv[0].second);
    Update b = make_update(storage_kv[1].first, storage_kv[1].second);
    Update c = make_update(storage_kv[2].first, storage_kv[2].second);
    UpdateList storage;
    storage.push_front(a);
    storage.push_front(b);
    storage.push_front(c);
    UpdateList state_changes;
    Update s1 =
        make_update(kv[0].first, kv[0].second, false, std::move(storage));
    Update s2 = make_update(kv[1].first, kv[1].second);
    state_changes.push_front(s1);
    state_changes.push_front(s2);
    auto block_num = 0x000000000001_hex;
    auto block_num2 = 00000000000002_hex;
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(block_num, {}, false, std::move(state_changes)));
    auto [state_it, end_nibble, res] =
        find_blocking(this->aux, *this->root, block_num);
    EXPECT_EQ(res, monad::mpt::find_result_msg::success);
    EXPECT_EQ(end_nibble, NibblesView{block_num}.nibble_size());
    EXPECT_EQ(
        state_it.node->data(),
        0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);

    { // update the block_num leaf's value and its nested subtrie
        UpdateList state_changes;
        state_changes.push_front(s2); // no change in nested state trie
        monad::byte_string const leaf_value = 0x01020304_hex;
        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(
                block_num, leaf_value, false, std::move(state_changes)));
        auto [state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, block_num);
        EXPECT_EQ(end_nibble, NibblesView{block_num}.nibble_size());
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(
            state_it.node->value(),
            leaf_value); // state_root leaf has updated
        EXPECT_EQ(
            state_it.node->data(), // hash for state trie remains the same
            0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);
    }
    // copy state root to block_num2
    this->root =
        copy_node(this->aux, std::move(this->root), block_num, block_num2);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(block_num2, monad::byte_string_view{}));
    {
        auto [state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, block_num2);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{block_num2}.nibble_size());
        EXPECT_EQ(
            state_it.node->data(),
            0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);
    }
    {
        auto [old_state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, block_num);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{block_num}.nibble_size());
        EXPECT_EQ(old_state_it.node->next(0), nullptr);
        EXPECT_EQ(
            old_state_it.node->data(),
            0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);
    }
    // copy state root to block_num3, update block_num3's leaf data
    auto block_num3 = 0x000000000003_hex;
    this->root =
        copy_node(this->aux, std::move(this->root), block_num2, block_num3);
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(block_num3, 0xdeadbeef03_hex));
    {
        auto [state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, block_num3);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{block_num3}.nibble_size());
        EXPECT_EQ(
            state_it.node->data(),
            0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);
        EXPECT_EQ(state_it.node->value(), 0xdeadbeef03_hex);
    }
    {
        auto [state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, block_num2);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{block_num2}.nibble_size());
        EXPECT_EQ(
            state_it.node->data(),
            0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);
        EXPECT_EQ(state_it.node->value(), monad::byte_string_view{});
    }
    // copy state root from block_num2 to block_num3 again. In on-disk trie
    // case, block_num2 leaf is on disk and block_num3 leaf in memory,
    // find_blocking() will read for leaf of block_num2, and update curr
    // block_num3 leaf to the same as block_num2.
    this->root =
        copy_node(this->aux, std::move(this->root), block_num2, block_num3);
    {
        auto [state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, block_num3);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{block_num3}.nibble_size());
        EXPECT_EQ(
            state_it.node->data(),
            0x9050b05948c3aab28121ad71b3298a887cdadc55674a5f234c34aa277fbd0325_hex);
        // leaf data changed here
        EXPECT_EQ(state_it.node->value(), monad::byte_string_view{});
    }
}

TYPED_TEST(TrieTest, verify_correct_compute_at_section_edge)
{
    this->sm = std::make_unique<StateMachineWithBlockNo>();

    auto const block_num1 = 0x000000000001_hex;
    auto const block_num2 = 0x000000000002_hex;
    auto const key = 0x123456_hex;
    auto const value = 0xdeadbeef_hex;

    UpdateList next;
    Update update = make_update(key, value);
    next.push_front(update);

    monad::byte_string_view const empty_value{};
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(block_num1, empty_value),
        make_update(block_num2, empty_value, false, std::move(next)));

    EXPECT_EQ(this->root->child_data_len(1), 0);
    EXPECT_EQ(this->root->child_data_len(), 0);

    // leaf is the end of block_num2 section, also root of account trie
    Node *const block_num2_leaf = this->root->next(1);
    EXPECT_EQ(block_num2_leaf->has_value(), true);
    EXPECT_EQ(block_num2_leaf->path_nibbles_len(), 0);
    EXPECT_EQ(block_num2_leaf->child_data_len(0), 10);
    EXPECT_EQ(block_num2_leaf->data().size(), 32);
    EXPECT_EQ(
        block_num2_leaf->data(),
        0x82efc3b165cba3705dec8fe0f7d8ec6692ae82605bdea6058d2237535dc6aa9b_hex);
}

TYPED_TEST(TrieTest, root_data_always_hashed)
{
    auto const key1 = 0x12_hex;
    auto const key2 = 0x13_hex;
    auto const value1 = 0xdead_hex;
    auto const value2 = 0xbeef_hex;
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(key1, value1),
        make_update(key2, value2));

    EXPECT_EQ(
        this->root_hash(),
        0xfb68c0ed148bf387cff736c64cc6acff3e89a6e6d722fba9b2eaf68f24ad5761_hex);
}

TYPED_TEST(TrieTest, aux_do_update_fixed_history_len)
{
    this->sm = std::make_unique<StateMachineWithBlockNo>();

    auto const &kv = fixed_updates::kv;
    uint64_t const start_block_id = 0x123;
    auto const prefix = 0x00_hex;

    auto upsert_same_kv_once = [&](uint64_t const block_id) {
        auto block_num = serialize_as_big_endian<BLOCK_NUM_BYTES>(block_id);
        auto u1 = make_update(kv[0].first, kv[0].second);
        auto u2 = make_update(kv[1].first, kv[1].second);
        UpdateList ul;
        ul.push_front(u1);
        ul.push_front(u2);

        auto u_prefix = Update{
            .key = prefix,
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = std::move(ul)};
        UpdateList ul_prefix;
        ul_prefix.push_front(u_prefix);
        this->root = this->aux.do_update(
            std::move(this->root),
            *this->sm,
            std::move(ul_prefix),
            block_id,
            true /*compaction*/);
        auto find_key = block_num + prefix;
        auto [state_it, end_nibble, res] =
            find_blocking(this->aux, *this->root, NibblesView{find_key});
        EXPECT_EQ(res, find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{find_key}.nibble_size());
        EXPECT_EQ(
            state_it.node->data(),
            0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
        // check db maintain expected historical versions
        if (this->aux.is_on_disk()) {
            if (block_id - start_block_id <
                UpdateAuxImpl::version_history_len) {
                EXPECT_EQ(
                    this->aux.max_version_in_db_history(*this->root) -
                        this->aux.min_version_in_db_history(*this->root),
                    block_id - start_block_id);
            }
            else {
                EXPECT_EQ(
                    this->aux.max_version_in_db_history(*this->root) -
                        this->aux.min_version_in_db_history(*this->root),
                    UpdateAuxImpl::version_history_len);
            }
        }
        else {
            EXPECT_EQ(
                this->aux.max_version_in_db_history(*this->root), block_id);
            EXPECT_EQ(
                this->aux.min_version_in_db_history(*this->root),
                start_block_id);
        }
    };
    for (uint64_t i = 0; i < 400; ++i) {
        upsert_same_kv_once(start_block_id + i);
    }
}

TYPED_TEST(TrieTest, variable_length_trie)
{
    this->sm = std::make_unique<StateMachineAlwaysVarLen>();

    auto const key0 = 0x80_hex;
    auto const key1 = 0x01_hex;
    auto const key16 = 0x10_hex;
    auto const key128 = 0x8180_hex;
    auto const key256 = 0x820100_hex;
    auto const keylong = 0x808182_hex;

    auto const value = 0xbeef_hex;

    // single element in trie
    this->root =
        upsert_updates(this->aux, *this->sm, {}, make_update(keylong, value));
    EXPECT_EQ(
        this->root_hash(),
        0x82a7b59bf8abe584aef31b580efaadbf19d0eba0e4ea8986e23db14ba9be6cb2_hex);

    // multiple keys
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(key0, value),
        make_update(key1, value),
        make_update(key16, value),
        make_update(key128, value),
        make_update(key256, value),
        make_update(keylong, value));

    EXPECT_EQ(
        this->root_hash(),
        0x162ce2fb5920c8d988691f4e826deb4f41951ea6343d4d8894b6ea3f5fbb4be0_hex);

    // longer value
    auto const long_value =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex;
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(key0, long_value),
        make_update(key1, long_value),
        make_update(key16, long_value),
        make_update(key128, long_value),
        make_update(key256, long_value),
        make_update(keylong, long_value));
    EXPECT_EQ(
        this->root_hash(),
        0x1a904a5579e7f301af64aeebbce5189b9df1e534fd2a4b642e604e92834a7611_hex);

    // find
    {
        auto [node0, end_nibble, res] =
            find_blocking(this->aux, *this->root, key0);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{key0}.nibble_size());
        EXPECT_EQ(node0.node->value(), long_value);
    }

    {
        auto [node_long, end_nibble, res] =
            find_blocking(this->aux, *this->root, keylong);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{keylong}.nibble_size());
        EXPECT_EQ(node_long.node->value(), long_value);
    }
}

TYPED_TEST(TrieTest, variable_length_trie_with_prefix)
{
    this->sm = std::make_unique<StateMachineVarLenTrieWithBlockNo>();

    auto const key0 = 0x80_hex;
    auto const key1 = 0x01_hex;
    auto const key16 = 0x10_hex;
    auto const key128 = 0x8180_hex;
    auto const key256 = 0x820100_hex;
    auto const keylong = 0x808182_hex;
    auto const value =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex;

    uint64_t const block_id = 0x123;
    auto const block_number_prefix =
        serialize_as_big_endian<BLOCK_NUM_BYTES>(block_id);

    std::list<Update> updates_alloc;
    UpdateList updates;

    updates.push_front(updates_alloc.emplace_back(make_update(key0, value)));
    updates.push_front(updates_alloc.emplace_back(make_update(key1, value)));
    updates.push_front(updates_alloc.emplace_back(make_update(key16, value)));
    updates.push_front(updates_alloc.emplace_back(make_update(key128, value)));
    updates.push_front(updates_alloc.emplace_back(make_update(key256, value)));
    updates.push_front(updates_alloc.emplace_back(make_update(keylong, value)));

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(
            block_number_prefix,
            monad::byte_string_view{},
            false,
            std::move(updates)));

    auto [root_it, end_nibble, res] =
        find_blocking(this->aux, NodeCursor{*this->root}, block_number_prefix);
    EXPECT_EQ(res, find_result_msg::success);
    EXPECT_EQ(end_nibble, BLOCK_NUM_NIBBLES_LEN);
    EXPECT_EQ(
        root_it.node->data(),
        0x1a904a5579e7f301af64aeebbce5189b9df1e534fd2a4b642e604e92834a7611_hex);

    // find
    {
        auto const find_key = block_number_prefix + key0;
        auto [node0, end_nibble, res] =
            find_blocking(this->aux, *this->root, find_key);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{find_key}.nibble_size());
        EXPECT_EQ(node0.node->value(), value);
    }

    {
        auto const find_key = block_number_prefix + keylong;
        auto [node_long, end_nibble, res] =
            find_blocking(this->aux, *this->root, find_key);
        EXPECT_EQ(res, monad::mpt::find_result_msg::success);
        EXPECT_EQ(end_nibble, NibblesView{find_key}.nibble_size());
        EXPECT_EQ(node_long.node->value(), value);
    }
}

TYPED_TEST(TrieTest, single_value_variable_length_trie_with_prefix)
{
    this->sm = std::make_unique<StateMachineVarLenTrieWithBlockNo>();

    uint64_t const block_id = 0x123;
    auto const block_number_prefix =
        serialize_as_big_endian<BLOCK_NUM_BYTES>(block_id);

    auto const keylong = 0x808182_hex;
    auto const value = 0xbeef_hex;

    UpdateList updates;
    Update u = make_update(keylong, value);
    updates.push_front(u);

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        {},
        make_update(
            block_number_prefix,
            monad::byte_string_view{},
            false,
            std::move(updates)));
    auto [root_it, end_nibble, res] =
        find_blocking(this->aux, NodeCursor{*this->root}, block_number_prefix);
    EXPECT_EQ(res, find_result_msg::success);
    EXPECT_EQ(end_nibble, BLOCK_NUM_NIBBLES_LEN);
    EXPECT_EQ(
        root_it.node->data(),
        0x82a7b59bf8abe584aef31b580efaadbf19d0eba0e4ea8986e23db14ba9be6cb2_hex);
}
