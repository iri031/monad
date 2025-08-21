#include <gtest/gtest.h>

#include <category/mpt2/config.hpp>
#include <category/mpt2/node_cursor.hpp>
#include <category/mpt2/test/test_fixtures.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/util.hpp>
#include <category/storage/config.hpp>
#include <category/storage/db_storage.hpp>
#include <category/storage/test/test_fixtures.hpp>
#include <category/storage/util.hpp>

#include <cstdint>
#include <cstring>
#include <filesystem>
#include <memory>

#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

using namespace MONAD_MPT2_NAMESPACE;
using namespace MONAD_STORAGE_NAMESPACE;
using namespace monad::storage_test;
using namespace monad::trie_test;

TEST_F(UpdateAuxFixture, upsert_write_transaction_works)
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

    { // read buffer directly from disk
        Node const *const root = aux.parse_node(root_offset);
        auto const node_size = root->get_disk_size();
        file_offset_t rd_offset =
            round_down_align<CPU_PAGE_BITS>(root_offset.raw());
        auto const buffer_off = root_offset.raw() - rd_offset;
        auto const bytes_to_read =
            round_up_align<CPU_PAGE_BITS>(rd_offset + node_size) - rd_offset;
        auto *const buffer = reinterpret_cast<unsigned char *>(
            aligned_alloc(DISK_PAGE_SIZE, bytes_to_read));
        auto const rd_fd = ::open(path.c_str(), O_RDONLY, O_CLOEXEC);
        ASSERT_TRUE(-1 != ::pread(rd_fd, buffer, bytes_to_read, rd_offset));
        Node const *const read_root = parse_node(buffer + buffer_off);
        EXPECT_TRUE(memcmp((void *)root, (void *)read_root, node_size) == 0);
    }

    EXPECT_EQ(aux.get_root_offset_at_version(version), root_offset);
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
    EXPECT_EQ(aux.db_history_max_version(), version);
    EXPECT_EQ(aux.get_root_offset_at_version(version), root_offset);
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
        aux.node_writer_offset_fast.add_to_offset(102423);
        aux.node_writer_offset_slow.add_to_offset(204858);
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

TEST_F(UpdateAuxFixture, fixed_history_length)
{
    auto const &kv = fixed_updates::kv;
    constexpr uint64_t history_len = 100;

    uint64_t const max_version = history_len * 2;
    uint64_t v = 0;
    chunk_offset_t root_offset{INVALID_OFFSET};
    {
        for (v = 0; v <= max_version; ++v) {
            WriteTransaction wt(aux);
            root_offset = upsert_updates(
                wt, root_offset, v, make_update(kv[0].first, kv[1].second));
            wt.finish(root_offset, v);
        }
        EXPECT_EQ(db_storage.db_history_max_version(false), max_version);
        EXPECT_EQ(db_storage.db_history_min_valid_version(), 0);
    }

    { // reopen with fixed length
        DbStorage storage{path, DbStorage::Mode::open_existing};
        UpdateAux aux2{storage, history_len};
        EXPECT_EQ(storage.db_history_max_version(false), max_version);
        EXPECT_EQ(
            storage.db_history_min_valid_version(),
            max_version - history_len + 1);

        {
            v = max_version + 1;
            WriteTransaction wt(aux);
            wt.finish(root_offset, v);
        }
        EXPECT_EQ(storage.db_history_max_version(false), v);
        EXPECT_EQ(storage.db_history_min_valid_version(), v - history_len + 1);
    }
}

TEST_F(UpdateAuxFixture, copy_trie)
{
    auto const &kv = fixed_updates::kv;
    chunk_offset_t root_offset{INVALID_OFFSET};
    uint64_t const src_version = 0;
    uint64_t const dest_version = 1;
    auto const src_prefix = 0x0012_hex;
    auto const dest_prefix = 0x001233_hex;

    DbStorage::creation_flags flags;
    flags.open_read_only = true;
    DbStorage ro_storage{path, DbStorage::Mode::open_existing, flags};
    UpdateAux aux_reader{ro_storage};

    {
        WriteTransaction wt(aux);
        root_offset = upsert_updates_with_prefix(
            wt,
            root_offset,
            src_prefix,
            src_version,
            make_update(kv[2].first, kv[2].second),
            make_update(kv[3].first, kv[3].second));
        EXPECT_EQ(ro_storage.db_history_max_version(false), INVALID_VERSION);
        wt.finish(root_offset, src_version);
    }

    EXPECT_EQ(ro_storage.db_history_max_version(false), src_version);
    EXPECT_EQ(ro_storage.get_root_offset_at_version(src_version), root_offset);

    {
        NodeCursor const root_cursor{*aux_reader.parse_node(root_offset)};
        auto const [cursor, res] = find(
            aux_reader, root_cursor, src_prefix + kv[2].first, src_version);
        EXPECT_EQ(res, find_result::success);
        EXPECT_EQ(cursor.node->value(), kv[2].second);
    }

    { // open wt to copy_trie
        WriteTransaction wt(aux);
        root_offset = wt.copy_trie(root_offset, src_prefix, 1, dest_prefix);
        EXPECT_EQ(ro_storage.db_history_max_version(false), src_version);
        wt.finish(root_offset, dest_version);
    }
    EXPECT_EQ(ro_storage.db_history_max_version(false), dest_version);

    {
        NodeCursor const root_cursor{*aux_reader.parse_node(root_offset)};
        auto const [cursor, res] = find(
            aux_reader, root_cursor, dest_prefix + kv[3].first, dest_version);
        EXPECT_EQ(res, find_result::success);
        EXPECT_EQ(cursor.node->value(), kv[3].second);
    }
}
