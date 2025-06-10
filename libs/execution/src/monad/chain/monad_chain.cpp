#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/block.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/inflight_expenses_buffer.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_block.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

evmc_revision MonadChain::get_revision() const
{
    return EVMC_CANCUN;
}

Result<void> MonadChain::validate_output_header(
    BlockHeader const &input, BlockHeader const &output) const
{
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }
    return success();
}

uint64_t MonadChain::compute_gas_refund(
    Transaction const &tx, uint64_t const gas_remaining,
    uint64_t const refund) const
{
    auto const monad_rev = get_monad_revision();
    if (MONAD_LIKELY(monad_rev >= MONAD_ONE)) {
        return 0;
    }
    else if (monad_rev == MONAD_ZERO) {
        auto const rev = get_revision();
        return g_star(rev, tx, gas_remaining, refund);
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

size_t MonadChain::get_max_code_size() const
{
    auto const monad_rev = get_monad_revision();
    if (MONAD_LIKELY(monad_rev >= MONAD_TWO)) {
        return 128 * 1024;
    }
    else if (monad_rev >= MONAD_ZERO) {
        return MAX_CODE_SIZE_EIP170;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

uint512_t get_inflight_expense(monad_revision const, Transaction const &tx)
{
    return tx.value + max_gas_cost(tx.gas_limit, tx.max_fee_per_gas);
}

uint256_t
get_max_reserve_balance(monad_revision const, Address const &sender, Db &db)
{
    std::optional<Account> const account = db.read_account(sender);
    if (account.has_value()) {
        return account.value().balance;
    }
    return 0;
}

Result<void> validate_block(
    Block const &block, std::vector<Address> const &senders,
    std::vector<uint256_t> const &max_reserve_balances,
    InflightExpensesBuffer const &inflight_expenses)
{
    MONAD_ASSERT(
        block.transactions.size() == senders.size() &&
        block.transactions.size() == max_reserve_balances.size());
    for (unsigned i = 0; i < senders.size(); ++i) {
        uint512_t const expense = inflight_expenses.sum(senders[i]);
        MONAD_ASSERT(expense);
        if (max_reserve_balances[i] < expense) {
            return BlockError::OutOfReserveBalance;
        }
    }
    return outcome::success();
}

MONAD_NAMESPACE_END
