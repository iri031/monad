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

#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <csignal>
#include <cstdint>

using namespace monad;

TEST(BlockDb, ReadNonExistingBlock)
{
    Block block;
    BlockDb const block_db(test_resource::correct_block_data_dir);
    // NO_BLOCK_FOUND
    EXPECT_FALSE(block_db.get(3u, block));
}

TEST(BlockDb, ReadNonDecompressableBlock)
{
    Block block;
    BlockDb const block_db(test_resource::bad_decompress_block_data_dir);
    // DECOMPRESS_ERROR
    EXPECT_EXIT(
        block_db.get(46'402u, block), testing::KilledBySignal(SIGABRT), "");
}

TEST(BlockDb, ReadNonDecodeableBlock)
{
    Block block;
    BlockDb const block_db(test_resource::bad_decode_block_data_dir);
    // DECODE_ERROR
    EXPECT_EXIT(
        block_db.get(46'402u, block), testing::KilledBySignal(SIGABRT), "");
}

TEST(BlockDb, DecompressBlock46402)
{
    uint64_t const block_number = 46'402;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}

TEST(BlockDb, DecompressBlock2730000)
{
    uint64_t const block_number = 2'730'000;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}

TEST(BlockDb, DecompressBlock2730001)
{
    uint64_t const block_number = 2'730'001;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}

TEST(BlockDb, DecompressBlock2730002)
{
    uint64_t const block_number = 2'730'002;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}

TEST(BlockDb, DecompressBlock2730009)
{
    uint64_t const block_number = 2'730'009;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}

TEST(BlockDb, Decompress14000000)
{
    uint64_t const block_number = 14'000'000;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}

TEST(BlockDb, DecompressBlock2397315)
{
    uint64_t const block_number = 2'397'315;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}
