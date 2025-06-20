#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

evmc_revision MonadChain::get_revision(
    uint64_t /* block_number */, uint64_t /* timestamp */) const
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
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, uint64_t const gas_remaining,
    uint64_t const refund) const
{
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_ONE)) {
        return 0;
    }
    else if (monad_rev == MONAD_ZERO) {
        auto const rev = get_revision(block_number, timestamp);
        return g_star(rev, tx, gas_remaining, refund);
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

size_t MonadChain::get_max_code_size(
    uint64_t const block_number, uint64_t const timestamp) const
{
    auto const monad_rev = get_monad_revision(block_number, timestamp);
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

uint256_t MonadChain::get_balance(
    uint64_t const block_number, uint64_t const timestamp, uint64_t const i,
    Address const &sender, State &state, void *const chain_context) const
{
    auto const acct = state.recent_account(sender);
    if (!acct.has_value()) {
        return 0;
    }
    auto const balance = acct.value().balance;
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_THREE)) {
        auto const &context = *static_cast<MonadChainContext *>(chain_context);
        auto const [cum_fee, _, num_fees] = context.fee_buffer.get(i, sender);
        if (acct.value().code_hash == NULL_HASH && num_fees == 1) {
            return balance;
        }
        auto const max_reserve = get_max_reserve(monad_rev, sender, state);
        MONAD_ASSERT(cum_fee <= max_reserve);
        auto const effective_reserve = max_reserve - uint256_t{cum_fee};
        return balance - std::min(balance, effective_reserve);
    }
    else if (monad_rev >= MONAD_ZERO) {
        return balance;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

Result<void> MonadChain::validate_transaction(
    uint64_t const block_number, uint64_t const timestamp, uint64_t const i,
    Transaction const &tx, Address const &sender, State &state,
    void *const chain_context) const
{
    auto const acct = state.recent_account(sender);
    auto res = ::monad::validate_transaction(tx, acct);
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_THREE)) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }
        auto const &context = *static_cast<MonadChainContext *>(chain_context);
        auto const [cum_fee, tx_fee, _] = context.fee_buffer.get(i, sender);
        MONAD_ASSERT(cum_fee >= tx_fee);
        uint512_t const cum_fees_without_tx = cum_fee - tx_fee;
        uint512_t const max_reserve = get_max_reserve(monad_rev, sender, state);
        uint512_t const balance = acct.has_value() ? acct.value().balance : 0;
        uint512_t const reserve = std::min(
            balance, max_reserve - std::min(max_reserve, cum_fees_without_tx));
        if (MONAD_UNLIKELY(tx_fee > reserve)) {
            return TransactionError::InsufficientReserveBalance;
        }
    }
    else if (monad_rev >= MONAD_ZERO) {
        return res;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
    return success();
}

uint256_t get_max_reserve(monad_revision const rev, Address const &, State &)
{
    // TODO: read from precompile
    return monad_default_max_reserve_balance(rev);
}

MONAD_NAMESPACE_END
