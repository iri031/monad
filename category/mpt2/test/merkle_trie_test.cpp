#include <gtest/gtest.h>

#include <category/mpt2/test/test_fixtures.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/update.hpp>

using namespace MONAD_MPT2_NAMESPACE;
using namespace monad::trie_test;

TEST_F(UpdateAuxFixture, simple_inserts)
{
    auto const &kv = fixed_updates::kv;

    auto root_offset = upsert_updates(
        aux,
        INVALID_OFFSET,
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));

    EXPECT_EQ(
        root_hash(root_offset),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    root_offset = upsert_updates(
        aux,
        root_offset,
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(
        root_hash(root_offset),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}

TEST_F(UpdateAuxFixture, insert_and_update)
{
    // keys are the same
    auto const key =
        0x1234567812345678123456781234567812345678123456781234567812345678_hex;
    auto const val1 =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex;
    auto const val2 =
        0xdeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddead_hex;

    // single update
    auto root_offset =
        upsert_updates(aux, INVALID_OFFSET, make_update(key, val1));
    EXPECT_EQ(
        root_hash(root_offset),
        0xa1aa368afa323866e03c21927db548afda3da793f4d3c646d7dd8109477b907e_hex);

    // update again
    root_offset = upsert_updates(aux, root_offset, make_update(key, val2));
    EXPECT_EQ(
        root_hash(root_offset),
        0x5d225e3b0f1f386171899d343211850f102fa15de6e808c6f614915333a4f3ab_hex);
}

TEST_F(EraseTrieFixture, none)
{
    EXPECT_EQ(
        this->root_hash(root_offset),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}

TEST_F(EraseTrieFixture, empty_update_list)
{
    // no update
    root_offset = upsert(aux, *sm, root_offset, {});
    EXPECT_EQ(
        this->root_hash(root_offset),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}

TEST_F(EraseTrieFixture, remove_everything)
{
    auto kv = fixed_updates::kv;

    std::vector<Update> update_vec;
    update_vec.reserve(kv.size());
    UpdateList ul;
    for (auto const &[k, v] : kv) {
        auto &u = update_vec.emplace_back(make_erase(k));
        ul.push_front(u);
    }
    root_offset = upsert(aux, *sm, root_offset, std::move(ul));

    EXPECT_EQ(
        this->root_hash(root_offset),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_hex);
}

TEST_F(EraseTrieFixture, delete_single_branch)
{
    auto kv = fixed_updates::kv;

    root_offset = upsert_updates(
        aux, root_offset, make_erase(kv[2].first), make_erase(kv[3].first));
    EXPECT_EQ(
        root_hash(root_offset),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);
}

TEST_F(EraseTrieFixture, delete_one_at_a_time)
{
    auto kv = fixed_updates::kv;

    root_offset = upsert_updates(aux, root_offset, make_erase(kv[2].first));
    EXPECT_EQ(
        root_hash(root_offset),
        0xd8b34a85db25148b1901459eac9805edadaa20b03f41fecd3b571f3b549e2774_hex);

    root_offset = upsert_updates(aux, root_offset, make_erase(kv[1].first));
    EXPECT_EQ(
        root_hash(root_offset),
        0x107c8dd7bf9e7ca1faaa2c5856b412a8d7fccfa0005ca2500673a86b9c1760de_hex);

    root_offset = upsert_updates(aux, root_offset, make_erase(kv[0].first));
    EXPECT_EQ(
        root_hash(root_offset),
        0x15fa9c02a40994d2d4f9c9b21daba3c4e455985490de5f9ae4889548f34d5873_hex);

    root_offset = upsert_updates(aux, root_offset, make_erase(kv[3].first));
    EXPECT_EQ(
        root_hash(root_offset),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_hex);
}
