// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_transaction_error.hpp>
#include <category/execution/monad/reserve_balance.h>

#include <algorithm>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t const i, bytes32_t const &orig_code_hash,
    std::array<
        std::reference_wrapper<std::vector<Address> const>,
        EXECUTION_DELAY> const &senders_per_block,
    std::array<
        std::reference_wrapper<std::vector<std::vector<Address>> const>,
        EXECUTION_DELAY> const &authorization_lists_per_block)
{
    if (orig_code_hash != NULL_HASH) { // check delegated
        return false;
    }

    for (size_t j = 0; j < 2; ++j) { // check pending blocks
        if (std::ranges::contains(senders_per_block[j].get(), sender)) {
            return false;
        }
        for (std::vector<Address> const &authorization_list :
             authorization_lists_per_block[j].get()) {
            if (std::ranges::contains(authorization_list, sender)) {
                return false;
            }
        }
    }

    for (size_t j = 0; j < i; ++j) { // check current block
        if (sender == senders_per_block[2].get()[j]) {
            return false;
        }
        if (std::ranges::contains(
                authorization_lists_per_block[2].get()[j], sender)) {
            return false;
        }
    }

    return true; // Allow dipping into reserve if no restrictions found
}

bool dipped_into_reserve(
    monad_revision const monad_rev, evmc_revision const rev,
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i,
    std::array<
        std::reference_wrapper<std::vector<Address> const>,
        EXECUTION_DELAY> const &senders_per_block,
    std::array<
        std::reference_wrapper<std::vector<std::vector<Address>> const>,
        EXECUTION_DELAY> const &authorization_lists_per_block,
    State &state)
{
    MONAD_ASSERT(i < senders_per_block[2].get().size());
    MONAD_ASSERT(i < authorization_lists_per_block[2].get().size());
    MONAD_ASSERT(
        senders_per_block.size() == authorization_lists_per_block.size());

    auto const &orig = state.original();
    for (auto const &[addr, stack] : state.current()) {
        MONAD_ASSERT(orig.contains(addr));
        std::optional<Account> const &orig_account = orig.at(addr).account_;
        bytes32_t const orig_code_hash = orig_account.has_value()
                                             ? orig_account.value().code_hash
                                             : NULL_HASH;

        // Skip if not EOA
        if (orig_code_hash != NULL_HASH) {
            // TODO: use the correct function when 7702 code is merged
            // vm::SharedIntercode const intercode =
            //    state.read_code(orig_code_hash)->intercode();
            // if (!evmone::is_code_delegated(
            //        {intercode->code(), intercode->code_size()})) {
            //    continue;
            //}
            continue;
        }

        // Skip if allowed to dip into reserve
        if (addr == sender && can_sender_dip_into_reserve(
                                  sender,
                                  i,
                                  orig_code_hash,
                                  senders_per_block,
                                  authorization_lists_per_block)) {
            continue;
        }

        // Check if dipped into reserve
        uint256_t const orig_balance =
            orig_account.has_value() ? orig_account.value().balance : 0;
        uint256_t const reserve =
            std::min(get_max_reserve(monad_rev, addr), orig_balance);
        uint256_t const violation_threshold =
            addr == sender ? reserve - uint256_t{tx.gas_limit} *
                                           gas_price(rev, tx, base_fee_per_gas)
                           : reserve;
        std::optional<Account> const &curr_account = stack.recent().account_;
        uint256_t const curr_balance =
            curr_account.has_value() ? curr_account.value().balance : 0;
        if (curr_balance < violation_threshold) {
            return true;
        }
    }
    return false;
}

MONAD_ANONYMOUS_NAMESPACE_END

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

bool MonadChain::get_create_inside_delegated() const
{
    return false;
}

Result<void> MonadChain::validate_transaction(
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &base_fee_per_gas) const
{
    auto const acct = state.recent_account(sender);
    auto res = ::monad::validate_transaction(tx, acct);
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        if (res.has_error() &&
            res.error() != TransactionError::InsufficientBalance) {
            return res;
        }
        evmc_revision const rev = get_revision(block_number, timestamp);
        uint512_t const balance = acct.has_value() ? acct.value().balance : 0;
        uint256_t const gas_fee =
            tx.gas_limit * gas_price(rev, tx, base_fee_per_gas);
        if (MONAD_UNLIKELY(balance < gas_fee)) {
            return MonadTransactionError::InsufficientBalanceForFee;
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

bool MonadChain::revert_transaction(
    uint64_t const block_number, uint64_t const timestamp,
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i, State &state,
    void *const chain_context) const
{
    auto const monad_rev = get_monad_revision(block_number, timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        auto const &ctx = *static_cast<MonadChainContext *>(chain_context);
        evmc_revision const rev = get_revision(block_number, timestamp);
        return dipped_into_reserve(
            monad_rev,
            rev,
            sender,
            tx,
            base_fee_per_gas,
            i,
            ctx.senders_per_block,
            ctx.authorization_lists_per_block,
            state);
    }
    else if (monad_rev >= MONAD_ZERO) {
        return false;
    }
    else {
        MONAD_ABORT("invalid revision for revert");
    }
}

uint256_t get_max_reserve(monad_revision const rev, Address const &)
{
    // TODO: implement precompile (support reading from orig)
    return monad_default_max_reserve_balance(rev);
}

MONAD_NAMESPACE_END
