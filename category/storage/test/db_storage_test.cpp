#include <gtest/gtest.h>

#include <category/core/assert.h>
#include <category/storage/config.hpp>
#include <category/storage/db_storage.hpp>
#include <category/storage/detail/scope_polyfill.hpp>
#include <category/storage/test/test_fixtures.hpp>
#include <category/storage/util.hpp>

#include <cstdint>
#include <filesystem>

#include <stdlib.h>
#include <unistd.h>

// tests
// 1. print summary
// 2. write to some chunks
// 3. check: read bytes and check as expected
// 4. destroy contents

using namespace MONAD_STORAGE_NAMESPACE;
using namespace monad::storage_test;

inline void run_test(std::filesystem::path const path)
{
    {
        DbStorage rw_storage(path, DbStorage::Mode::truncate);
        EXPECT_EQ(rw_storage.num_chunks(), 4092);
        EXPECT_FALSE(rw_storage.is_read_only());
        EXPECT_TRUE(rw_storage.is_newly_truncated());

        // write something
        auto *data = rw_storage.get_data(chunk_offset_t{0, 1024});
        for (size_t i = 0; i < 1024; ++i) {
            data[i] = static_cast<unsigned char>(i % 256);
        }
    }
    // reopen with read only
    {
        DbStorage::creation_flags options;
        options.open_read_only = true;
        DbStorage ro_storage{path, DbStorage::Mode::open_existing, options};
        EXPECT_EQ(ro_storage.num_chunks(), 4092);
        EXPECT_TRUE(ro_storage.is_read_only());
        EXPECT_FALSE(ro_storage.is_newly_truncated());

        auto const *data = ro_storage.get_data(chunk_offset_t{0, 1024});
        for (size_t i = 0; i < 1024; ++i) {
            EXPECT_EQ(data[i], static_cast<unsigned char>(i % 256));
        }
    }

    // reopen to append
    {
        DbStorage rw_storage(path, DbStorage::Mode::open_existing);
        EXPECT_EQ(rw_storage.num_chunks(), 4092);
        EXPECT_FALSE(rw_storage.is_read_only());
        EXPECT_FALSE(rw_storage.is_newly_truncated());

        auto const *data = rw_storage.get_data(chunk_offset_t{0, 1024});
        for (size_t i = 0; i < 1024; ++i) {
            EXPECT_EQ(data[i], static_cast<unsigned char>(i % 256));
        }

        auto *data2 = rw_storage.get_data(
            chunk_offset_t{(uint32_t)rw_storage.num_chunks() - 1, 0});
        for (size_t i = 0; i < 1024; ++i) {
            data2[i] = static_cast<unsigned char>(i % 256);
        }
    }
}

TEST(DbStorage, anonymous_node_works)
{
    DbStorage rw_storage(use_anonymous_inode_tag{}, 1UL << 40 /* 1Tb */);
    EXPECT_EQ(rw_storage.num_chunks(), 4092);
    EXPECT_FALSE(rw_storage.is_read_only());

    // write something
    auto *data = rw_storage.get_data(chunk_offset_t{0, 1024});
    for (size_t i = 0; i < 1024; ++i) {
        data[i] = static_cast<unsigned char>(i % 256);
    }
    // read back
    auto const *ro_data = rw_storage.get_data(chunk_offset_t{0, 1024});
    for (size_t i = 0; i < 1024; ++i) {
        EXPECT_EQ(ro_data[i], static_cast<unsigned char>(i % 256));
    }
}

TEST(DbStorage, file_works)
{
    // truncate to 1Tb
    auto const path = create_temp_test_file(1024);
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(path); });

    run_test(path);
}

TEST_F(DbStorageFixture, root_offsets)
{
    auto const root_offsets_capacity = db_storage.root_offsets().capacity();
    EXPECT_EQ(root_offsets_capacity, 1 << 25);

    EXPECT_EQ(db_storage.db_history_max_version(), INVALID_VERSION);
    EXPECT_EQ(db_storage.version_history_length(), 1 << 25);

    chunk_offset_t const offset0{1, 0};
    db_storage.append_root_offset(offset0);
    EXPECT_EQ(db_storage.db_history_max_version(), 0);
    EXPECT_EQ(db_storage.get_root_offset_at_version(0), offset0);

    chunk_offset_t offset1{2, 0};
    db_storage.append_root_offset(offset1);
    EXPECT_EQ(db_storage.db_history_max_version(), 1);
    EXPECT_EQ(db_storage.get_root_offset_at_version(1), offset1);
    offset1.offset = 1024;
    db_storage.update_root_offset(1, offset1);
    EXPECT_EQ(db_storage.db_history_max_version(), 1);
    EXPECT_EQ(db_storage.get_root_offset_at_version(1), offset1);
    EXPECT_EQ(db_storage.db_history_min_valid_version(), 0);
    EXPECT_EQ(db_storage.db_history_range_lower_bound(), 0);

    DbStorage::creation_flags options;
    options.open_read_only = true;
    DbStorage const ro_storage(path, DbStorage::Mode::open_existing, options);
    EXPECT_EQ(ro_storage.version_history_length(), 1 << 25);
    EXPECT_EQ(ro_storage.root_offsets().max_version(), 1);
    EXPECT_EQ(ro_storage.get_root_offset_at_version(0), offset0);
    EXPECT_EQ(ro_storage.get_root_offset_at_version(1), offset1);

    // root offsets wrap around
    auto const version = root_offsets_capacity * 2;
    db_storage.fast_forward_next_version(version);
    for (auto v = version; v < version + 100; ++v) {
        chunk_offset_t offset{100, v - version};
        db_storage.append_root_offset(offset);
        EXPECT_EQ(db_storage.db_history_max_version(), v);
        EXPECT_EQ(db_storage.db_history_min_valid_version(), version);
        EXPECT_EQ(ro_storage.get_root_offset_at_version(v), offset);
    }
}

TEST(DbStorage, db_metadata_chunk_list_op)
{
    auto const path = create_temp_test_file(1024);
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(path); });

    DbStorage rw_storage(path, DbStorage::Mode::truncate);
    EXPECT_EQ(rw_storage.num_chunks(), 4092);
    EXPECT_FALSE(rw_storage.is_read_only());

    auto const *const m = rw_storage.db_metadata();
    auto strip_free_chunk_append_to =
        [&](DbStorage::chunk_list const list) -> uint32_t {
        auto const idx = m->free_list.end;
        rw_storage.remove(idx);
        rw_storage.append(list, idx);
        return idx;
    };

    // Append free chunks to fast and slow lists
    uint32_t total_fast = (uint32_t)m->fast_list_begin()->insertion_count() + 1;
    uint32_t total_slow = (uint32_t)m->slow_list_begin()->insertion_count() + 1;
    while (m->free_list_begin() !=
           m->free_list_end()) { // at least 2 free chunks
        auto const fast_list_end =
            strip_free_chunk_append_to(DbStorage::chunk_list::fast);
        auto const slow_list_end =
            strip_free_chunk_append_to(DbStorage::chunk_list::slow);
        EXPECT_TRUE(m->at(fast_list_end)->in_fast_list);
        EXPECT_TRUE(m->at(slow_list_end)->in_slow_list);
        EXPECT_EQ(m->fast_list.end, fast_list_end);
        EXPECT_EQ(m->slow_list.end, slow_list_end);
        EXPECT_EQ(m->at(fast_list_end)->insertion_count(), total_fast);
        EXPECT_EQ(m->at(slow_list_end)->insertion_count(), total_slow);
        ++total_fast;
        ++total_slow;
    }
    // remove all fast chunks and append to free
    while (m->fast_list_begin() != nullptr) {
        auto const idx = m->fast_list.begin;
        rw_storage.remove(idx);
        rw_storage.append(DbStorage::chunk_list::free, idx);
        --total_fast;
        EXPECT_FALSE(m->at(idx)->in_fast_list);
        EXPECT_FALSE(m->at(idx)->in_slow_list);
    }
    ASSERT_EQ(total_fast, 0);
    // remove all slow chunks and append to free
    while (m->slow_list_begin() != nullptr) {
        auto const idx = m->slow_list.begin;
        rw_storage.remove(idx);
        rw_storage.append(DbStorage::chunk_list::free, idx);
        --total_slow;
        EXPECT_FALSE(m->at(idx)->in_fast_list);
        EXPECT_FALSE(m->at(idx)->in_slow_list);
    }
    ASSERT_EQ(total_slow, 0);

    uint32_t total_free = 0;
    auto const *ci = m->free_list_begin();
    while (ci != nullptr) {
        ++total_free;
        EXPECT_FALSE(ci->in_fast_list);
        EXPECT_FALSE(ci->in_slow_list);
        ci = ci->next(m);
    }
    EXPECT_EQ(total_free, rw_storage.num_chunks());
}

// TEST(destroy_contents) {}
