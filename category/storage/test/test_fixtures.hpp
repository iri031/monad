#pragma once

#include <category/storage/db_storage.hpp>
#include <category/storage/util.hpp>

#include <filesystem>

#include <gtest/gtest.h>
#include <stdlib.h>
#include <unistd.h>

namespace monad::storage_test
{
    std::filesystem::path create_temp_test_file(long size_gb)
    {
        std::filesystem::path const filename{
            MONAD_STORAGE_NAMESPACE::working_temporary_directory() /
            "monad_test_XXXXXX"};
        int const fd = ::mkstemp((char *)filename.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(-1 != ::ftruncate(fd, size_gb * 1024 * 1024 * 1024));
        ::close(fd);
        return filename;
    }

    struct DbStorageFixture : public ::testing::Test
    {
        std::filesystem::path const path;
        MONAD_STORAGE_NAMESPACE::DbStorage db_storage;

        DbStorageFixture()
            : path{create_temp_test_file(8)}
            , db_storage(
                  path, MONAD_STORAGE_NAMESPACE::DbStorage::Mode::truncate)
        {
        }

        ~DbStorageFixture() noexcept
        {
            std::filesystem::remove(path);
        }
    };
}
