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

#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/core/monad_block.hpp>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <filesystem>

namespace
{
    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            std::filesystem::temp_directory_path() /
            "monad_db_snapshot_test_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        monad::OnDiskMachine machine;
        monad::mpt2::Db const db{
            machine,
            monad::mpt2::OnDiskDbConfig{.append = false, .dbname_path = path}};
        return dbname;
    }
}

TEST(DbBinarySnapshot, Basic)
{
    using namespace monad;
    using namespace monad::mpt2;

    auto const src_db = tmp_dbname();

    bytes32_t root;
    Code code_delta;
    BlockHeader last_header;
    {
        OnDiskMachine machine;
        mpt2::Db db{machine, mpt2::OnDiskDbConfig{.dbname_path = src_db}};
        for (uint64_t i = 0; i < 100; ++i) {
            load_header(db, BlockHeader{.number = i});
        }
        db.update_finalized_version(99);
        StateDeltas deltas;
        uint64_t num_deltas = 10;
        for (uint64_t i = 0; i < num_deltas; ++i) {
            StorageDeltas storage;
            if ((i % 100) == 0) {
                for (uint64_t j = 0; j < 10; ++j) {
                    storage.emplace(
                        bytes32_t{j}, StorageDelta{bytes32_t{}, bytes32_t{j}});
                }
            }
            deltas.emplace(
                Address{i},
                StateDelta{
                    .account =
                        {std::nullopt, Account{.balance = i, .nonce = i}},
                    .storage = storage});
        }
        for (uint64_t i = 0; i < 1'000; ++i) {
            std::vector<uint64_t> const bytes(100, i);
            byte_string_view const code{
                reinterpret_cast<unsigned char const *>(bytes.data()),
                bytes.size() * sizeof(uint64_t)};
            bytes32_t const hash = to_bytes(keccak256(code));
            auto const icode = vm::make_shared_intercode(code);
            code_delta.emplace(hash, icode);
        }
        TrieDb tdb{db};
        tdb.commit(
            deltas, code_delta, bytes32_t{100}, BlockHeader{.number = 100});
        tdb.finalize(100, bytes32_t{100});
        last_header = tdb.read_eth_header();
        root = tdb.state_root();
    }

    auto const dest_db = tmp_dbname();
    {
        auto const root = std::filesystem::temp_directory_path() / "snapshot";
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                root.c_str(), 100);
        EXPECT_TRUE(monad_db_dump_snapshot(
            src_db.c_str(),
            static_cast<unsigned>(-1),
            100,
            monad_db_snapshot_write_filesystem,
            context));

        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        monad_db_snapshot_load_filesystem(
            dest_db.c_str(), static_cast<unsigned>(-1), root.c_str(), 100);

        std::filesystem::remove_all(root);
    }

    {
        RODb db{dest_db};
        TrieRODb tdb{db};
        for (uint64_t i = 0; i < 100; ++i) {
            tdb.set_block_and_prefix(i);
            EXPECT_EQ(tdb.read_eth_header(), BlockHeader{.number = i});
        }
        tdb.set_block_and_prefix(100);
        EXPECT_EQ(tdb.read_eth_header(), last_header);
        EXPECT_EQ(tdb.state_root(), root);
        for (auto const &[hash, icode] : code_delta) {
            auto const from_db = tdb.read_code(hash);
            ASSERT_TRUE(from_db);
            EXPECT_EQ(
                byte_string_view(from_db->code(), from_db->code_size()),
                byte_string_view(icode->code(), icode->code_size()));
        }
    }

    std::filesystem::remove(src_db);
    std::filesystem::remove(dest_db);
}
