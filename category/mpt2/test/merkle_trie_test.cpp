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
        *sm,
        INVALID_OFFSET,
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second));

    EXPECT_EQ(
        root_hash(aux.parse_node(root_offset)),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    root_offset = upsert_updates(
        aux,
        *sm,
        root_offset,
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));
    EXPECT_EQ(
        root_hash(aux.parse_node(root_offset)),
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
        upsert_updates(aux, *sm, INVALID_OFFSET, make_update(key, val1));
    EXPECT_EQ(
        root_hash(aux.parse_node(root_offset)),
        0xa1aa368afa323866e03c21927db548afda3da793f4d3c646d7dd8109477b907e_hex);

    // update again
    root_offset = upsert_updates(aux, *sm, root_offset, make_update(key, val2));
    EXPECT_EQ(
        root_hash(aux.parse_node(root_offset)),
        0x5d225e3b0f1f386171899d343211850f102fa15de6e808c6f614915333a4f3ab_hex);
}

// TODO: erase
