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
#include <monad/execution/monad_precompiles.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint256_t default_max_reserve_balance(monad_revision)
{
    return 1;
}

MONAD_ANONYMOUS_NAMESPACE_END

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

std::optional<evmc::Result>
MonadChain::check_call_precompile(evmc_message const &msg, State &state) const
{
    auto maybe_result =
        check_call_monad_precompile(get_monad_revision(), msg, state);
    if (maybe_result.has_value()) {
        return maybe_result;
    }
    return ::monad::check_call_precompile(get_revision(), msg);
}

uint512_t get_inflight_expense(monad_revision const, Transaction const &tx)
{
    return tx.value + max_gas_cost(tx.gas_limit, tx.max_fee_per_gas);
}

uint256_t
get_max_reserve_balance(monad_revision const rev, Address const &sender, Db &db)
{
    MONAD_ASSERT(rev >= MONAD_THREE);
    std::optional<Account> const account = db.read_account(sender);
    if (!account.has_value()) {
        return 0;
    }
    bytes32_t const val = db.read_storage(
        MAX_RESERVE_BALANCE_ADDRESS,
        account.value().incarnation,
        to_bytes(to_byte_string_view(sender.bytes)));
    Result<uint256_t> const res = rlp::decode_raw_num<uint256_t>(
        rlp::zeroless_view(to_byte_string_view(val.bytes)));
    MONAD_ASSERT(res.has_value());
    uint256_t const max_reserve =
        res.value() == 0 ? default_max_reserve_balance(rev) : res.value();
    return std::min(account.value().balance, max_reserve);
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
