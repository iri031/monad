#include "gtest/gtest.h"

#include <category/mpt2/state_machine.hpp>
#include <category/mpt2/test/test_fixtures.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/util.hpp>
#include <category/storage/db_storage.hpp>
#include <category/storage/test/test_fixtures.hpp>
#include <category/storage/util.hpp>

#include <filesystem>
#include <memory>

#include "unistd.h"

using namespace MONAD_MPT2_NAMESPACE;
using namespace MONAD_STORAGE_NAMESPACE;
using namespace monad::storage_test;
using namespace monad::trie_test;

TEST_F(UpdateAuxFixture, upsert_works)
{
    auto const &kv = fixed_updates::kv;

    chunk_offset_t root_offset{INVALID_OFFSET};
    uint64_t version = 0;
    {
        WriteTransaction wt(aux);
        UpdateList update_ls;
        Update u1 = make_update(kv[0].first, kv[0].second),
               u2 = make_update(kv[1].first, kv[1].second);
        update_ls.push_front(u1);
        update_ls.push_front(u2);
        root_offset = wt.do_upsert(
            INVALID_OFFSET, *sm, std::move(update_ls), version, false, true);
        wt.finish(root_offset, version);
    }

    EXPECT_EQ(
        aux.db_storage().get_root_offset_at_version(version), root_offset);
    NodeCursor const root_cursor{*aux.parse_node(root_offset)};
    // find
    auto const [cursor, res] = find(aux, root_cursor, kv[0].first, version);
    EXPECT_EQ(res, find_result::success);
    EXPECT_EQ(cursor.node->value(), kv[0].second);

    ++version;
    { // version 1
        WriteTransaction wt(aux);
        UpdateList update_ls;
        Update u1 = make_update(kv[2].first, kv[2].second),
               u2 = make_update(kv[3].first, kv[3].second);
        update_ls.push_front(u1);
        update_ls.push_front(u2);
        root_offset = wt.do_upsert(
            root_offset, *sm, std::move(update_ls), version, false, true);
        wt.finish(root_offset, version);
    }
    EXPECT_EQ(aux.db_storage().db_history_max_version(), version);
    EXPECT_EQ(
        aux.db_storage().get_root_offset_at_version(version), root_offset);
    NodeCursor const root_cursor2{*aux.parse_node(root_offset)};
    for (auto i : {0, 1, 2, 3}) {
        auto const [cursor, res] =
            find(aux, root_cursor2, kv[i].first, version);
        EXPECT_EQ(res, find_result::success);
        EXPECT_EQ(cursor.node->value(), kv[i].second);
    }
}

TEST_F(DbStorageFixture, reopen_with_correct_writer_offsets_to_start_with)
{
    chunk_offset_t expected_fast_offset{0, 0}, expected_slow_offset{0, 0};
    {
        UpdateAux aux{db_storage};
        aux.node_writer_offset_fast.add_to_offset(1024);
        aux.node_writer_offset_slow.add_to_offset(2048);
        expected_fast_offset = aux.node_writer_offset_fast;
        expected_slow_offset = aux.node_writer_offset_slow;

        WriteTransaction wt(aux);
        wt.finish(aux.node_writer_offset_fast, 0);

        EXPECT_EQ(
            db_storage.db_metadata()->db_offsets.start_of_wip_offset_fast,
            aux.node_writer_offset_fast);
        EXPECT_EQ(
            db_storage.db_metadata()->db_offsets.start_of_wip_offset_slow,
            aux.node_writer_offset_slow);

        aux.node_writer_offset_fast =
            aux.node_writer_offset_fast.add_to_offset(100);
        aux.node_writer_offset_slow =
            aux.node_writer_offset_slow.add_to_offset(200);
    }

    DbStorage storage{path, DbStorage::Mode::open_existing};
    EXPECT_EQ(
        storage.db_metadata()->db_offsets.start_of_wip_offset_fast,
        expected_fast_offset);
    EXPECT_EQ(
        storage.db_metadata()->db_offsets.start_of_wip_offset_slow,
        expected_slow_offset);
}

TEST_F(DbStorageFixture, fixed_history_length)
{
    constexpr uint64_t history_len = 100;

    chunk_offset_t offset{0, 0};
    uint64_t const max_version = history_len * 2;
    uint64_t v = 0;

    {
        UpdateAux aux(db_storage);
        for (v = 0; v <= max_version; ++v) {
            WriteTransaction wt(aux);
            wt.finish(offset, v);
            offset = offset.add_to_offset(100);
        }
        EXPECT_EQ(db_storage.db_history_max_version(), max_version);
        EXPECT_EQ(db_storage.db_history_min_valid_version(), 0);
    }

    { // reopen with fixed length
        DbStorage storage{path, DbStorage::Mode::open_existing};
        UpdateAux aux{storage, history_len};
        EXPECT_EQ(storage.db_history_max_version(), max_version);
        EXPECT_EQ(
            storage.db_history_min_valid_version(),
            max_version - history_len + 1);

        {
            v = max_version + 1;
            WriteTransaction wt(aux);
            wt.finish(offset, v);
        }
        EXPECT_EQ(storage.db_history_max_version(), v);
        EXPECT_EQ(storage.db_history_min_valid_version(), v - history_len + 1);
    }
}
