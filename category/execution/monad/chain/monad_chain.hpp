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

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/monad/chain/monad_revision.h>

#include <evmc/evmc.h>

#include <array>
#include <functional>
#include <vector>

MONAD_NAMESPACE_BEGIN

inline constexpr unsigned EXECUTION_DELAY = 3;

struct BlockHeader;
struct Transaction;
class AccountState;
class FeeBuffer;

struct MonadChainContext
{
    std::array<
        std::reference_wrapper<std::vector<Address> const>, EXECUTION_DELAY>
        senders_per_block;
    std::array<
        std::reference_wrapper<std::vector<std::vector<Address>> const>,
        EXECUTION_DELAY>
        authorization_lists_per_block;
};

struct MonadChain : Chain
{
    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const override;

    virtual monad_revision
    get_monad_revision(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual size_t
    get_max_code_size(uint64_t block_number, uint64_t timestamp) const override;

    virtual bool get_create_inside_delegated() const override;

    virtual Result<void> validate_transaction(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        Address const &sender, State &,
        uint256_t const &base_fee_per_gas) const override;

    virtual bool revert_transaction(
        uint64_t block_number, uint64_t timestamp, Address const &sender,
        Transaction const &, uint256_t const &base_fee_per_gas, uint64_t i,
        State &, void *chain_context) const override;
};

uint256_t get_max_reserve(monad_revision, Address const &);

MONAD_NAMESPACE_END
