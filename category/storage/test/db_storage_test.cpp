#include "gtest/gtest.h"

#include <category/core/assert.h>
#include <category/storage/config.hpp>
#include <category/storage/db_storage.hpp>
#include <category/storage/detail/scope_polyfill.hpp>
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

// db_metadata test:
// append(fast)
// free()

// root offset test, TODO: finish impl
// write to root offset, get root offset
// test wrap around case, test different root offset capacity?

using namespace MONAD_STORAGE_NAMESPACE;

std::filesystem::path create_temp_file(long size_gb)
{
    std::filesystem::path const filename{
        working_temporary_directory() / "monad_storage_test_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, size_gb * 1024 * 1024 * 1024));
    ::close(fd);
    return filename;
}

inline void run_test(std::filesystem::path const path)
{
    // TODO: write to offset
    // TODO: append/remove chunk list in db_metadata
    {
        DbStorage::creation_flags options;
        DbStorage rw_storage(path, DbStorage::Mode::truncate, options);
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
}

TEST(DbStorage, file_works)
{
    // truncate to 1Tb
    auto const path = create_temp_file(1024);
    auto undb = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(path); });

    run_test(path);
}
