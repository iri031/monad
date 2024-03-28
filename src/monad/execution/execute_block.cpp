#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/fmt/block_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/fmt/trace_fmt.hpp>
#include <monad/execution/trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <quill/detail/LogMacros.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

// EIP-4895
constexpr void process_withdrawal(
    State &state, std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    if (withdrawals.has_value()) {
        for (auto const &withdrawal : withdrawals.value()) {
            state.add_to_balance(
                withdrawal.recipient,
                uint256_t{withdrawal.amount} * uint256_t{1'000'000'000u});
        }
    }
}

inline void transfer_balance_dao(BlockState &block_state)
{
    State state{block_state};

    for (auto const &addr : dao::child_accounts) {
        auto const balance = intx::be::load<uint256_t>(state.get_balance(addr));
        state.add_to_balance(dao::withdraw_account, balance);
        state.subtract_from_balance(addr, balance);
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);
}

constexpr Receipt::Bloom compute_bloom(std::vector<Receipt> const &receipts)
{
    Receipt::Bloom bloom{};
    for (auto const &receipt : receipts) {
        for (unsigned i = 0; i < 256; ++i) {
            bloom[i] |= receipt.bloom[i];
        }
    }

    return bloom;
}

inline void
commit(BlockState &block_state, std::vector<Receipt> const &receipts = {})
{
    block_state.log_debug();

    block_state.commit(receipts);
}

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block(
    Block &block, Db &db, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    TRACE_BLOCK_EVENT(StartBlock);

    BlockState block_state{db};

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(block_state);
        }
    }

    std::shared_ptr<std::optional<Result<Receipt>>[]> results{
        new std::optional<Result<Receipt>>[block.transactions.size()]};

    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[block.transactions.size() + 1]};
    promises[0].set_value();

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i = i,
             results = results,
             promises = promises,
             &transaction = block.transactions[i],
             &header = block.header,
             &block_hash_buffer = block_hash_buffer,
             &block_state] {
                results[i] = execute<rev>(
                    i,
                    transaction,
                    header,
                    block_hash_buffer,
                    block_state,
                    promises[i]);
                promises[i + 1].set_value();
            });
    }

    auto const last = static_cast<std::ptrdiff_t>(block.transactions.size());
    promises[last].get_future().wait();

    std::vector<Receipt> receipts;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_LIKELY(results[i].value().has_value())) {
            receipts.emplace_back(results[i].value().value());
        }
        else { // Use UINT64_T MAX to indicate validation error
            receipts.emplace_back(
                Receipt{.status = std::numeric_limits<uint64_t>::max()});
            LOG_ERROR(
                "Error in validatating transaction {}, with error = {}",
                i,
                results[i].value().assume_error().message());
        }
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &receipt : receipts) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    // TODO: Probably needs to disable these 2 checks for now for devnet? (They
    // won't pass if any txn fails validation) YP eq. 33
    if (compute_bloom(receipts) != block.header.logs_bloom) {
        return BlockError::WrongLogsBloom;
    }

    // YP eq. 170
    if (cumulative_gas_used != block.header.gas_used) {
        return BlockError::InvalidGasUsed;
    }

    State state{block_state};
    if constexpr (rev >= EVMC_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    apply_block_reward<rev>(block_state, block);

    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    commit(block_state, receipts);

    return receipts;
}

EXPLICIT_EVMC_REVISION(execute_block);

MONAD_NAMESPACE_END
