#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db_snapshot.h>
#include <monad/db/db_snapshot_filesystem.h>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <test_resource_data.h>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>

#include <filesystem>

namespace
{
    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_db_snapshot_test_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        monad::OnDiskMachine machine;
        monad::mpt::Db const db{
            machine,
            monad::mpt::OnDiskDbConfig{
                .append = false, .dbname_paths = {path}}};
        return dbname;
    }
}

TEST(DbBinarySnapshot, Basic)
{
    using namespace monad;
    using namespace monad::mpt;

    auto const src_db = tmp_dbname();

    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(14'000'000u, block);
    ASSERT_TRUE(res);
    auto const transactions = block.transactions;

    bytes32_t root;
    Code code_delta;
    std::vector<BlockHeader> expected_headers;
    {
        OnDiskMachine machine;
        mpt::Db db{machine, OnDiskDbConfig{.dbname_paths = {src_db}}};
        TrieDb tdb{db};
        for (uint64_t i = 0; i < 100; ++i) {
            tdb.commit(
                StateDeltas{},
                Code{},
                MonadConsensusBlockHeader::from_eth_header(
                    BlockHeader{.number = i}),
                std::vector<Receipt>{transactions.size()},
                std::vector<std::vector<CallFrame>>{transactions.size()},
                std::vector<Address>{transactions.size()},
                transactions);
            tdb.finalize(i, i);
            tdb.set_block_and_round(i);
            expected_headers.emplace_back(tdb.read_eth_header());
        }
        byte_string const code(100, 'h');
        bytes32_t const hash = to_bytes(keccak256(code));
        auto const analysis = std::make_shared<CodeAnalysis>(analyze(code));
        code_delta.emplace(hash, analysis);
        tdb.commit(
            StateDeltas{
                {Address{100},
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 100, .nonce = 100}},
                     .storage =
                         StorageDeltas{
                             {bytes32_t{}, {bytes32_t{}, bytes32_t{100}}}}}}},
            Code{{hash, analysis}},
            MonadConsensusBlockHeader::from_eth_header(
                BlockHeader{.number = 100}),
            std::vector<Receipt>{transactions.size()},
            std::vector<std::vector<CallFrame>>{transactions.size()},
            std::vector<Address>{transactions.size()},
            transactions);
        tdb.finalize(100, 100);
        tdb.set_block_and_round(100);
        expected_headers.emplace_back(tdb.read_eth_header());
        code_delta.emplace(hash, analysis);
        root = tdb.state_root();
    }

    auto const dest_db = tmp_dbname();
    {
        auto const root = std::filesystem::temp_directory_path() / "snapshot";
        auto *const context =
            monad_db_snapshot_filesystem_write_user_context_create(
                root.c_str(), 100);
        char const *dbname_paths[] = {src_db.c_str()};
        ASSERT_TRUE(monad_db_dump_snapshot(
            dbname_paths,
            1,
            static_cast<unsigned>(-1),
            100,
            monad_db_snapshot_write_filesystem,
            context));

        monad_db_snapshot_filesystem_write_user_context_destroy(context);

        char const *dbname_paths_new[] = {dest_db.c_str()};
        monad_db_snapshot_load_filesystem(
            dbname_paths_new, 1, static_cast<unsigned>(-1), root.c_str(), 100);

        std::filesystem::remove_all(root);
    }

    {
        AsyncIOContext io_context{
            ReadOnlyOnDiskDbConfig{.dbname_paths = {dest_db}}};
        mpt::Db db{io_context};
        TrieDb tdb{db};
        for (uint64_t i = 0; i <= 100; ++i) {
            tdb.set_block_and_round(i);
            EXPECT_EQ(tdb.read_eth_header(), expected_headers.at(i));
            if (i == 99 || i == 100) {
                auto const txns = read_transactions(db, i);
                MONAD_ASSERT(txns.has_value());
                byte_string_view enc{txns.value()};
                auto const decoded_txns = rlp::decode_transaction_list(enc);
                MONAD_ASSERT(decoded_txns.has_value());
                EXPECT_EQ(decoded_txns.value(), transactions);
            }
        }
        EXPECT_EQ(tdb.state_root(), root);
        for (auto const &[hash, analysis] : code_delta) {
            auto const from_db = tdb.read_code(hash);
            ASSERT_TRUE(from_db);
            EXPECT_EQ(from_db->executable_code(), analysis->executable_code());
        }
    }

    std::filesystem::remove(src_db);
    std::filesystem::remove(dest_db);
}
