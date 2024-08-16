#include <monad/config.hpp>
#include <monad/db/block_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/rpc/eth_call.hpp>

#include <gtest/gtest.h>

#include <chrono>
#include <filesystem>
#include <vector>

#include <iostream>

using namespace monad;

TEST(EthCall, rate)
{
    uint64_t const block_number = 12'000'000u;
    BlockDb const block_db{"/home/jhunsaker/block_db"};
    Block block{};
    ASSERT_TRUE(block_db.get(block_number, block));

    std::vector<Transaction> const& txns = block.transactions;
    std::vector<Address> senders;

    for(unsigned i = 0; i < txns.size() ; ++i){
        auto const sender = recover_sender(txns[i]);
        ASSERT_TRUE(sender.has_value());
        senders.emplace_back(sender.value());
    }

    BlockHashBuffer block_hash_buffer;
    for (uint64_t i = block_number < 256 ? 1 : block_number - 255; i < block_number;) {
        Block curr_block;
        ASSERT_TRUE(block_db.get(i, curr_block));
        block_hash_buffer.set(i - 1, curr_block.header.parent_hash);
        ++i;
    }
    std::vector<std::filesystem::path> db_path{"/dev/nvme1n1"};
    int failed_cnt = 0;

    auto const start_time = std::chrono::steady_clock::now();
    for(unsigned i = 0; i < 10'000u; ++i){
        Transaction const& txn = txns[i % txns.size()];
        auto const res = eth_call_impl(txn, block.header, block_number, senders[i % txns.size()], block_hash_buffer, db_path);
        EXPECT_TRUE(res.has_value());
        if (!res.has_value()){
            ++failed_cnt;
        }
    }

    auto const finish_time = std::chrono::steady_clock::now();

    auto const time_elasped = std::chrono::duration_cast<std::chrono::milliseconds>(finish_time - start_time);

    std::cerr << "Time elasped: " << static_cast<uint64_t>(time_elasped.count()) << std::endl;
    std::cerr << "Failed count: " << failed_cnt << std::endl;
}