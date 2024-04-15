#pragma once

#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/config.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/result.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>

#include <boost/outcome/try.hpp>

#include <quill/Quill.h>

#include <test_resource_data.h>

#include <cstdint>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

class ReplayFromBlockDb
{
public:
    uint64_t n_transactions{0};

    bool verify_root_hash(
        evmc_revision const rev, BlockHeader const &block_header,
        bytes32_t /* transactions_root */, bytes32_t const receipts_root,
        bytes32_t const state_root) const
    {
        if (state_root != block_header.state_root) {
            LOG_ERROR(
                "Block: {}, Computed State Root: {}, Expected State Root: {}",
                block_header.number,
                state_root,
                block_header.state_root);
            return false;
        }
        if (MONAD_LIKELY(rev >= EVMC_BYZANTIUM)) {
            if (receipts_root != block_header.receipts_root) {
                LOG_ERROR(
                    "Block: {}, Computed Receipts Root: {}, Expected Receipts "
                    "Root: {}",
                    block_header.number,
                    receipts_root,
                    block_header.receipts_root);
                return false;
            }
        }
        return true;
    }

    Result<uint64_t> run_fork(
        DbRW &db, BlockDb &block_db, BlockHashBuffer &block_hash_buffer,
        fiber::PriorityPool &priority_pool, uint64_t const start_block_number,
        uint64_t const nblocks)
    {
        MONAD_ASSERT(start_block_number);

        EthereumMainnet const chain{};

        int freq = 1000;
        int count = freq;
        uint64_t txns = 0;
        auto tbegin = std::chrono::steady_clock::now();

        uint64_t i = 0;
        for (; i < nblocks; ++i) {
            uint64_t const block_number = start_block_number + i;
            if (MONAD_UNLIKELY(!block_number)) {
                break; // wrapped
            }

            Block block{};
            if (!block_db.get(block_number, block)) {
                return i;
            }

            block_hash_buffer.set(block_number - 1, block.header.parent_hash);

            {
                auto result = chain.static_validate_header(block.header);
                if (MONAD_UNLIKELY(result.has_error())) {
                    LOG_ERROR(
                        "block {} {}",
                        block.header.number,
                        result.assume_error().message().c_str());
                    return std::move(result).assume_error();
                }
            }

            evmc_revision const rev = chain.get_revision(block.header);

            BOOST_OUTCOME_TRY(static_validate_block(rev, block));

            auto const receipts =
                execute_block(rev, block, db, block_hash_buffer, priority_pool);

            n_transactions += block.transactions.size();

            if (!verify_root_hash(
                    rev,
                    block.header,
                    NULL_ROOT,
                    db.receipts_root(),
                    db.state_root())) {
                return BlockError::WrongStateRoot;
            }
            if (--count == 0) {
                auto tnow = std::chrono::steady_clock::now();
                auto const elapsed =
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        tnow - tbegin)
                        .count();
                uint64_t tps = (n_transactions - txns) * 1'000'000 /
                               static_cast<uint64_t>(elapsed);
                char str[100];
                sprintf(
                    str,
                    "%d blocks to %8ld: %6ld tx %5ld tps",
                    freq,
                    start_block_number + i,
                    (n_transactions - txns),
                    tps);
                LOG_INFO("{}", str);
                count = freq;
                txns = n_transactions;
                tbegin = tnow;
            }
        }

        return i;
    }

    Result<uint64_t>
    run(DbRW &db, BlockDb &block_db, fiber::PriorityPool &priority_pool,
        uint64_t const start_block_number, uint64_t const nblocks)
    {
        Block block{};

        BlockHashBuffer block_hash_buffer;
        uint64_t block_number =
            start_block_number < 256 ? 1 : start_block_number - 255;
        for (; block_number < start_block_number; ++block_number) {
            block = Block{};
            bool const result = block_db.get(block_number, block);
            MONAD_ASSERT(result);
            block_hash_buffer.set(block_number - 1, block.header.parent_hash);
        }

        return run_fork(
            db,
            block_db,
            block_hash_buffer,
            priority_pool,
            start_block_number,
            nblocks);
    }
};

MONAD_NAMESPACE_END
