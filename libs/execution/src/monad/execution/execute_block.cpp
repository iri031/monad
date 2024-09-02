#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/fmt/transaction_fmt.hpp>
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
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/future.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
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

inline void
transfer_balance_dao(BlockState &block_state, Incarnation const incarnation)
{
    State state{block_state, incarnation};

    for (auto const &addr : dao::child_accounts) {
        auto const balance = intx::be::load<uint256_t>(state.get_balance(addr));
        state.add_to_balance(dao::withdraw_account, balance);
        state.subtract_from_balance(addr, balance);
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);
}

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block(
    Chain const &chain, Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    TRACE_BLOCK_EVENT(StartBlock);

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(
                block_state, Incarnation{block.header.number, 0});
        }
    }

    std::shared_ptr<std::optional<Result<Receipt>>[]> const results{
        new std::optional<Result<Receipt>>[block.transactions.size()]};

    std::shared_ptr<fiber::simple_promise<void>[]> const promises {
        new fiber::simple_promise<void>[block.transactions.size() + 1]};
    promises[0].set_value();

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [&chain = chain,
             i = i,
             results = results,
             promises = promises,
             &transaction = block.transactions[i],
             &header = block.header,
             &block_hash_buffer = block_hash_buffer,
             &block_state] {
                // While we're running this task, change the name of the fiber
                // hosting it to include the suffix " [B:<block-no> T:<i>]"
                monad_fiber_t *const fiber = monad_fiber_self();
                const size_t prefix_len = std::strlen(fiber->name);
                (void)snprintf(fiber->name + prefix_len,
                               sizeof fiber->name - prefix_len, " [B:%lu T:%u]",
                               header.number, i);

                // Set the debug name of promise[i] "txn_wb_<i>", the
                // transaction wait barrier for transaction i
                promises[i].set_debug_name(fmt::format("txn_wb_{}", i));
                results[i] = execute<rev>(
                    chain,
                    i,
                    transaction,
                    header,
                    block_hash_buffer,
                    block_state,
                    promises[i]);
                promises[i + 1].set_value();

                // We're done, chop the block:txn suffix off the fiber name
                fiber->name[prefix_len] = '\0';
            });
    }

    auto const last = static_cast<std::ptrdiff_t>(block.transactions.size());
    promises[last].get_future().wait();

    std::vector<Receipt> receipts;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_UNLIKELY(results[i].value().has_error())) {
            LOG_ERROR(
                "tx {} validation failed: {}",
                i,
                results[i].value().assume_error().message().c_str());
            LOG_ERROR("failed tx: {}", block.transactions[i]);
        }
        BOOST_OUTCOME_TRY(Receipt receipt, std::move(results[i].value()));
        receipts.push_back(std::move(receipt));
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &receipt : receipts) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (rev >= EVMC_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    apply_block_reward<rev>(state, block);

    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    return receipts;
}

EXPLICIT_EVMC_REVISION(execute_block);

Result<std::vector<Receipt>> execute_block(
    Chain const &chain, evmc_revision const rev, Block &block,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    SWITCH_EVMC_REVISION(
        execute_block,
        chain,
        block,
        block_state,
        block_hash_buffer,
        priority_pool);
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
