#include "event.hpp"
#include "runloop_replay.hpp"

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/core/procfs/statm.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <quill/Quill.h>

#include <algorithm>
#include <chrono>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

void log_tps(
    uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
    uint64_t const gas, std::chrono::steady_clock::time_point const begin)
{
    auto const now = std::chrono::steady_clock::now();
    auto const elapsed = std::max(
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
                .count()),
        1UL); // for the unlikely case that elapsed < 1 mic
    uint64_t const tps = (ntxs) * 1'000'000 / elapsed;
    uint64_t const gps = gas / elapsed;

    LOG_INFO(
        "Run {:4d} blocks to {:8d}, number of transactions {:6d}, "
        "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
        nblocks,
        block_num,
        ntxs,
        tps,
        gps,
        monad_procfs_self_resident() / (1L << 20));
};

#pragma GCC diagnostic pop

// Processing a historical Ethereum block encompasses all the following
// actions:
//
//   1. block header input validation
//   2. sender address recovery
//   3. "core" execution: transaction-level EVM execution that tracks state
//      changes, but does not commit them
//   4. database commit of state changes (incl. Merkle root calculations)
//   5. post-commit validation of header, with Merkle root fields filled in
//   6. immediate database finalization of the proposal
//   7. computation of block hash, appending it to the circular hash buffer
//   8. emitting a block metrics log line
static Result<BlockExecOutput> process_ethereum_block(
    Chain const &chain, monad_chain_config const chain_config, Db &db, vm::VM &vm,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, Block &block, bytes32_t const &block_id,
    bytes32_t const &parent_block_id)
{
    [[maybe_unused]] auto const block_start = std::chrono::system_clock::now();
    auto const block_begin = std::chrono::steady_clock::now();
    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

    evmc_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);

    BOOST_OUTCOME_TRY(static_validate_block(rev, block));

    size_t const transaction_count = block.transactions.size();
    std::vector<boost::fibers::promise<void>> txn_sync_barriers(
        transaction_count);

    auto const sender_recovery_begin = std::chrono::steady_clock::now();
    auto const recovered_senders =
        recover_senders(block.transactions, priority_pool, txn_sync_barriers);
    [[maybe_unused]] auto const sender_recovery_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - sender_recovery_begin);

    std::vector<Address> senders(transaction_count);
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        if (recovered_senders[i].has_value()) {
            senders[i] = recovered_senders[i].value();
        }
        else {
            return TransactionError::MissingSender;
        }
    }

    db.set_block_and_prefix(block.header.number - 1, parent_block_id);

    BlockExecOutput exec_output;
    BlockMetrics block_metrics;
    BlockState block_state(db, vm);
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_PERF_EVM_ENTER);
    BOOST_OUTCOME_TRY(
        auto results,
        execute_block(
            chain,
            rev,
            block,
            senders,
            block_state,
            block_hash_buffer,
            priority_pool,
            block_metrics,
            txn_sync_barriers));
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_PERF_EVM_EXIT);

    std::vector<Receipt> receipts(results.size());
    std::vector<std::vector<CallFrame>> call_frames(results.size());
    for (unsigned i = 0; i < results.size(); ++i) {
        auto &result = results[i];
        receipts[i] = std::move(result.receipt);
        call_frames[i] = std::move(result.call_frames);
    }

    block_state.log_debug();
    auto const commit_begin = std::chrono::steady_clock::now();
    block_state.commit(
        block_id,
        block.header,
        receipts,
        call_frames,
        senders,
        block.transactions,
        block.ommers,
        block.withdrawals);
    [[maybe_unused]] auto const commit_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - commit_begin);

    exec_output.eth_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, exec_output.eth_header));


    // For monad chain replay, we also need to check for state and receipt
    // roots
    // Note: This is not ideal, but minimize changes to live runloop
    if (chain_config != CHAIN_CONFIG_ETHEREUM_MAINNET) {
        if (MONAD_UNLIKELY(
                block.header.state_root != exec_output.eth_header.state_root)) {
            LOG_ERROR(
                "State root mismatch at block {}", block.header.number);
            return BlockError::WrongMerkleRoot;
        }
        if (MONAD_UNLIKELY(
                block.header.receipts_root !=
                exec_output.eth_header.receipts_root)) {
            LOG_ERROR(
                "Receipt root mismatch at block {}", block.header.number);
            return BlockError::WrongMerkleRoot;
        }
    }

    db.finalize(block.header.number, block_id);
    db.update_verified_block(block.header.number);

    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));
    block_hash_buffer.set(
        exec_output.eth_header.number, exec_output.eth_block_hash);

    [[maybe_unused]] auto const block_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - block_begin);
    LOG_INFO(
        "__exec_block,bl={:8},ts={}"
        ",tx={:5},rt={:4},rtp={:5.2f}%"
        ",sr={:>7},txe={:>8},cmt={:>8},tot={:>8},tpse={:5},tps={:5}"
        ",gas={:9},gpse={:4},gps={:3}{}",
        block.header.number,
        std::chrono::duration_cast<std::chrono::milliseconds>(
            block_start.time_since_epoch())
            .count(),
        block.transactions.size(),
        block_metrics.num_retries(),
        100.0 * (double)block_metrics.num_retries() /
            std::max(1.0, (double)block.transactions.size()),
        sender_recovery_time,
        block_metrics.tx_exec_time(),
        commit_time,
        block_time,
        block.transactions.size() * 1'000'000 /
            (uint64_t)std::max(1L, block_metrics.tx_exec_time().count()),
        block.transactions.size() * 1'000'000 /
            (uint64_t)std::max(1L, block_time.count()),
        exec_output.eth_header.gas_used,
        exec_output.eth_header.gas_used /
            (uint64_t)std::max(1L, block_metrics.tx_exec_time().count()),
        exec_output.eth_header.gas_used /
            (uint64_t)std::max(1L, block_time.count()),
        db.print_stats());

    return exec_output;
}

// Historical Ethereum replay does not have consensus events like the Monad
// chain, but we emit dummy versions because it reduces the difference for
// event consuming code that waits to see a particular commitment state (e.g.,
// finalized) before acting; the "blockcap" helper library (which only records
// finalized blocks) is an example. This does not try to imitate the pipelined
// operation of the Monad chain's consensus events
void emit_consensus_events(bytes32_t const &block_id, uint64_t block_number)
{
    monad_exec_block_qc const qc = {
        .block_tag = {.id = block_id, .block_number = block_number},
        .round = block_number + 1,
        .epoch = 0};
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_QC, qc);

    monad_exec_block_finalized const finalized_info = {
        .id = block_id, .block_number = block_number};
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_FINALIZED, finalized_info);

    monad_exec_block_verified const verified_info = {
        .block_number = block_number};
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_VERIFIED, verified_info);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::pair<uint64_t, uint64_t>> runloop_replay(
    Chain const &chain, monad_chain_config const chain_config, std::filesystem::path const &ledger_dir, Db &db,
    vm::VM &vm, BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    uint64_t const batch_size =
        end_block_num == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;
    uint256_t const chain_id = chain.get_chain_id();
    BlockDb block_db(ledger_dir);
    bytes32_t parent_block_id{};

    while (block_num <= end_block_num && stop == 0) {
        Block block;
        MONAD_ASSERT_PRINTF(
            block_db.get(chain_config, block_num, block),
            "Could not query %lu from blockdb",
            block_num);

        bytes32_t const block_id = bytes32_t{block_num};
        record_block_exec_start(
            block_id,
            chain_id,
            block.header.parent_hash,
            block.header,
            block.header.number,
            0,
            size(block.transactions));

        BOOST_OUTCOME_TRY(
            BlockExecOutput const exec_output,
            record_block_exec_result(process_ethereum_block(
                chain,
                chain_config,
                db,
                vm,
                block_hash_buffer,
                priority_pool,
                block,
                block_id,
                parent_block_id)));

        emit_consensus_events(block_id, block_num);
        ntxs += block.transactions.size();
        batch_num_txs += block.transactions.size();
        total_gas += block.header.gas_used;
        batch_gas += block.header.gas_used;
        ++batch_num_blocks;

        if (block_num % batch_size == 0) {
            log_tps(
                block_num,
                batch_num_blocks,
                batch_num_txs,
                batch_gas,
                batch_begin);
            batch_num_blocks = 0;
            batch_num_txs = 0;
            batch_gas = 0;
            batch_begin = std::chrono::steady_clock::now();
        }
        parent_block_id = block_id;
        ++block_num;
    }
    if (batch_num_blocks > 0) {
        log_tps(
            block_num, batch_num_blocks, batch_num_txs, batch_gas, batch_begin);
    }
    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
