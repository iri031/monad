#include "runloop_monad.hpp"
#include "event.hpp"
#include "file_io.hpp"

#include <monad/chain/chain.hpp>
#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/event/exec_event_ctypes.h>
#include <monad/core/event/exec_event_recorder.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/execution/wal_reader.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/metrics/block_metrics.hpp>
#include <monad/mpt/db.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <filesystem>
#include <iterator>
#include <optional>
#include <span>
#include <thread>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

void log_tps(
    uint64_t const block_num, bytes32_t const &block_id, uint64_t const ntxs,
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
        "Run to block= {:4d}, block_id {}, number of "
        "transactions {:6d}, "
        "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
        block_num,
        block_id,
        ntxs,
        tps,
        gps,
        monad_procfs_self_resident() / (1L << 20));
};

#pragma GCC diagnostic pop

struct MonadVoteCommon
{
    uint64_t round;
    uint64_t epoch;
    bytes32_t id;
};

MonadVoteCommon get_common_vote_fields(
    std::variant<MonadVoteV1, MonadVoteV2> const &vote_variant)
{
    return std::visit(
        overloaded{
            [](MonadVoteV1 const &v1) {
                return MonadVoteCommon{
                    .round = v1.round, .epoch = v1.epoch, .id = v1.id};
            },
            [](MonadVoteV2 const &v2) {
                return MonadVoteCommon{
                    .round = v2.round, .epoch = v2.epoch, .id = v2.id};
            }},
        vote_variant);
}

void record_monad_block_qc(
    MonadConsensusBlockHeader const &consensus_header,
    uint64_t finalized_block_num)
{
    // Before recording a QC for block B, we need to check if that block isn't
    // already finalized. The reason for this check is the following sequence:
    //
    //   - we execute proposed block B1
    //
    //   - execution begins to fall behind, while consensus advances; B1
    //     receives a QC (upon the proposal of B2) and B2 also received a QC
    //     (upon proposal of B3), finalizing B1; the execution daemon is still
    //     working on B1 during this time (or more likely, is restarting after
    //     a crash that occurs immediately after B1 has executed)
    //
    //   - by the time execution is ready to execute another proposed block,
    //     consensus has finalized B1; this is communicated to the execution
    //     daemon, and finalize logic takes precedence and runs immediately,
    //     emitting a BLOCK_FINALIZED event
    //
    //   - during the execution of B2, we'll see the QC for B1. Since it has
    //     already been finalized, we'll skip it
    uint64_t const vote_block_number = consensus_header.seqno - 1;
    if (vote_block_number <= finalized_block_num) {
        return;
    }
    MonadVoteCommon const &vote_common =
        get_common_vote_fields(consensus_header.qc.vote);
    monad_exec_block_qc const qc = {
        .block_tag = {.id = vote_common.id, .block_number = vote_block_number},
        .round = vote_common.round,
        .epoch = vote_common.epoch};
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_QC, qc);
}

void init_block_hash_chain_proposals(
    MonadChain const &chain, mpt::Db &db, BlockHashChain &block_hash_chain,
    uint64_t const start_block_num)
{
    uint64_t const end_block_num = db.get_latest_version();
    for (uint64_t b = start_block_num; b <= end_block_num; ++b) {
        for (bytes32_t const &id : get_proposal_block_ids(db, b)) {
            auto const consensus_header =
                read_consensus_header(chain, db, b, proposal_prefix(id));
            MONAD_ASSERT_PRINTF(
                consensus_header.has_value(),
                "Could not decode consensus block at %lu block_id %s",
                b,
                fmt::format("{}", id).c_str());
            auto const encoded_eth_header =
                db.get(mpt::concat(proposal_prefix(id), BLOCKHEADER_NIBBLE), b);
            MONAD_ASSERT(encoded_eth_header.has_value());
            block_hash_chain.propose(
                to_bytes(keccak256(encoded_eth_header.value())),
                b,
                id,
                consensus_header.value().parent_id());
        }
    }
}

bool has_executed(
    MonadChain const &chain, mpt::Db const &db,
    MonadConsensusBlockHeader const &header, bytes32_t const &block_id)
{
    auto const prefix = proposal_prefix(block_id);
    return header == read_consensus_header(chain, db, header.seqno, prefix);
}

bool validate_delayed_execution_results(
    BlockHashBuffer const &block_hash_buffer,
    std::vector<BlockHeader> const &execution_results)
{
    if (MONAD_UNLIKELY(execution_results.empty())) {
        return true;
    }

    uint64_t expected_block_number = execution_results.front().number;
    for (auto const &result : execution_results) {
        if (MONAD_UNLIKELY(expected_block_number != result.number)) {
            LOG_ERROR(
                "Validated blocks not increasing. Expected block {}, got block "
                "{}",
                expected_block_number,
                result.number);
            return false;
        }

        auto const block_hash =
            to_bytes(keccak256(rlp::encode_block_header(result)));
        if (MONAD_UNLIKELY(
                block_hash != block_hash_buffer.get(result.number))) {
            LOG_ERROR(
                "Delayed execution result mismatch for block {}",
                result.number);
            return false;
        }
        expected_block_number = result.number + 1;
    }
    return true;
}

Result<BlockExecOutput> propose_block(
    bytes32_t const &block_id,
    MonadConsensusBlockHeader const &consensus_header, Block block,
    BlockHashChain &block_hash_chain, MonadChain const &chain, Db &db,
    vm::VM &vm, fiber::PriorityPool &priority_pool, bool const is_first_block)
{
    [[maybe_unused]] auto const block_start = std::chrono::system_clock::now();
    auto const block_begin = std::chrono::steady_clock::now();
    auto const &block_hash_buffer =
        block_hash_chain.find_chain(consensus_header.parent_id());

    BOOST_OUTCOME_TRY(chain.static_validate_consensus_header(consensus_header));

    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

    evmc_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);

    BOOST_OUTCOME_TRY(static_validate_block(rev, block));

    db.set_block_and_prefix(
        block.header.number - 1,
        is_first_block ? bytes32_t{} : consensus_header.parent_id());

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
        call_frames[i] = (std::move(result.call_frames));
    }

    block_state.log_debug();
    auto const commit_begin = std::chrono::steady_clock::now();
    block_state.commit(
        block_id,
        consensus_header,
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

    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));

    [[maybe_unused]] auto const block_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - block_begin);
    LOG_INFO(
        "__exec_block,bl={:8},id={},ts={}"
        ",tx={:5},rt={:4},rtp={:5.2f}%"
        ",sr={:>7},txe={:>8},cmt={:>8},tot={:>8},tpse={:5},tps={:5}"
        ",gas={:9},gpse={:4},gps={:3}{}",
        block.header.number,
        block_id,
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

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    MonadChain const &chain, std::filesystem::path const &ledger_dir,
    mpt::Db &raw_db, Db &db, vm::VM &vm,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &finalized_block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);
    uint64_t const start_block_num = finalized_block_num;
    uint256_t const chain_id = chain.get_chain_id();
    BlockHashChain block_hash_chain(block_hash_buffer);
    init_block_hash_chain_proposals(
        chain, raw_db, block_hash_chain, start_block_num);

    auto const body_dir = ledger_dir / "bodies";
    auto const header_dir = ledger_dir / "headers";
    auto const proposed_head = header_dir / "proposed_head";
    auto const finalized_head = header_dir / "finalized_head";

    uint64_t total_gas = 0;
    uint64_t ntxs = 0;

    struct ToExecute
    {
        bytes32_t block_id;
        MonadConsensusBlockHeader header;
    };

    struct ToFinalize
    {
        uint64_t block;
        bytes32_t block_id;
        std::vector<uint64_t> verified_blocks;
    };

    std::deque<ToExecute> to_execute;
    std::deque<ToFinalize> to_finalize;

    MONAD_ASSERT(
        raw_db.get_latest_finalized_version() != mpt::INVALID_BLOCK_NUM);

    while (finalized_block_num < end_block_num && stop == 0) {
        bytes32_t id;
        MonadConsensusBlockHeader header;
        to_finalize.clear();
        to_execute.clear();

        uint64_t const last_finalized_by_execution =
            raw_db.get_latest_finalized_version();

        // read from finalized head if we are behind
        id = head_pointer_to_id(finalized_head);
        if (MONAD_LIKELY(id != bytes32_t{})) {
            uint64_t block_number;
            do {
                auto const block_id = id;
                header = read_header(chain, id, header_dir);
                id = header.parent_id();
                block_number = header.seqno;

                if (MONAD_UNLIKELY(header.seqno > end_block_num)) {
                    continue;
                }
                bool const needs_finalize =
                    header.seqno > last_finalized_by_execution;
                if (needs_finalize) {
                    std::vector<uint64_t> verified_blocks;
                    for (BlockHeader const &h :
                         header.delayed_execution_results) {
                        verified_blocks.push_back(h.number);
                    }
                    to_finalize.push_front(ToFinalize{
                        .block = header.seqno,
                        .block_id = block_id,
                        .verified_blocks = std::move(verified_blocks)});
                }

                if (!has_executed(chain, raw_db, header, block_id)) {
                    MONAD_ASSERT(needs_finalize);
                    to_execute.push_front(ToExecute{
                        .block_id = block_id, .header = std::move(header)});
                }
            }
            while (block_number - 1 > last_finalized_by_execution);
        }

        // try reading from proposal head if we are caught up
        if (to_finalize.empty()) {
            id = head_pointer_to_id(proposed_head);
            if (MONAD_LIKELY(id != bytes32_t{})) {
                for (;;) {
                    header = read_header(chain, id, header_dir);
                    if (header.seqno <= last_finalized_by_execution) {
                        break;
                    }
                    auto const parent_id = header.parent_id();
                    if (header.seqno <= end_block_num &&
                        !has_executed(chain, raw_db, header, id)) {
                        to_execute.push_front(ToExecute{
                            .block_id = id, .header = std::move(header)});
                    }
                    id = parent_id;
                }

                // Before executing this proposal chain, verify we are on the
                // latest canonical chain. Note that this condition doesn't hold
                // when no blocks have been finalized because consensus starts
                // at block 1 with a parent_id of 0x0, but will work after the
                // finalized_head points to a block with seqno >= 1.
                if (!to_execute.empty()) {
                    auto const &first_header = to_execute.front().header;
                    MONAD_ASSERT_PRINTF(
                        first_header.seqno - 1 >= last_finalized_by_execution,
                        "first header seqno %lu, last_finalized_by_execution "
                        "%lu",
                        first_header.seqno,
                        last_finalized_by_execution);
                    bool const on_canonical_chain =
                        query_consensus_header(
                            raw_db,
                            last_finalized_by_execution,
                            finalized_nibbles)
                            .transform([&first_header](
                                           byte_string const &header_data) {
                                return to_bytes(blake3(header_data)) ==
                                       first_header.parent_id();
                            })
                            .value_or(false);
                    if (MONAD_UNLIKELY(!on_canonical_chain)) {
                        to_execute.clear();
                    }
                }
            }
        }

        if (MONAD_UNLIKELY(to_execute.empty() && to_finalize.empty())) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }

        for (auto const &[block_id, consensus_header] : to_execute) {
            auto const block_time_start = std::chrono::steady_clock::now();

            uint64_t const block_number =
                consensus_header.execution_inputs.number;
            MonadConsensusBlockBody const consensus_body =
                read_body(consensus_header.block_body_id, body_dir);
            auto const ntxns = consensus_body.transactions.size();

            auto const &block_hash_buffer =
                block_hash_chain.find_chain(consensus_header.parent_id());

            record_monad_block_qc(consensus_header, finalized_block_num);
            record_block_exec_start(
                block_id,
                chain_id,
                block_hash_buffer.get(consensus_header.seqno - 1),
                consensus_header.execution_inputs,
                consensus_header.block_round,
                consensus_header.epoch,
                ntxns);

            MONAD_ASSERT(validate_delayed_execution_results(
                block_hash_buffer, consensus_header.delayed_execution_results));

            BOOST_OUTCOME_TRY(
                BlockExecOutput const exec_output,
                record_block_exec_result(propose_block(
                    block_id,
                    consensus_header,
                    Block{
                        .header = consensus_header.execution_inputs,
                        .transactions = std::move(consensus_body.transactions),
                        .ommers = std::move(consensus_body.ommers),
                        .withdrawals = std::move(consensus_body.withdrawals)},
                    block_hash_chain,
                    chain,
                    db,
                    vm,
                    priority_pool,
                    block_number == start_block_num)));
            block_hash_chain.propose(
                exec_output.eth_block_hash,
                block_number,
                block_id,
                consensus_header.parent_id());

            db.update_voted_metadata(
                consensus_header.seqno - 1, consensus_header.parent_id());

            log_tps(
                block_number,
                block_id,
                ntxns,
                exec_output.eth_header.gas_used,
                block_time_start);
        }

        for (auto const &[block, block_id, verified_blocks] : to_finalize) {
            LOG_INFO(
                "Processing finalization for block {} with block_id {}",
                block,
                block_id);
            db.finalize(block, block_id);
            block_hash_chain.finalize(block_id);
            monad_exec_block_finalized const finalized_info = {
                .id = block_id, .block_number = block};
            record_exec_event(
                std::nullopt, MONAD_EXEC_BLOCK_FINALIZED, finalized_info);
            finalized_block_num = block;

            if (!verified_blocks.empty() &&
                verified_blocks.back() != mpt::INVALID_BLOCK_NUM) {
                db.update_verified_block(verified_blocks.back());
            }
            for (uint64_t b : verified_blocks) {
                if (b == 0 || b == mpt::INVALID_BLOCK_NUM) {
                    continue;
                }
                monad_exec_block_verified const verified_info = {
                    .block_number = b};
                record_exec_event(
                    std::nullopt, MONAD_EXEC_BLOCK_VERIFIED, verified_info);
            }
        }
    }

    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
