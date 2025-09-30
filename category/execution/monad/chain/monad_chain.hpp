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
#include <category/vm/evm/monad/revision.h>

#include <ankerl/unordered_dense.h>
#include <evmc/evmc.h>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

inline constexpr size_t MAX_CODE_SIZE_MONAD_TWO = 128 * 1024;
inline constexpr size_t MAX_INITCODE_SIZE_MONAD_FOUR =
    2 * MAX_CODE_SIZE_MONAD_TWO;

struct BlockHeader;
struct Transaction;
class AccountState;

struct MonadChainContext
{
    ankerl::unordered_dense::segmented_set<Address> const
        *grandparent_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> const
        *parent_senders_and_authorities;
    ankerl::unordered_dense::segmented_set<Address> const
        &senders_and_authorities;
    std::vector<Address> const &senders;
    std::vector<std::vector<std::optional<Address>>> const &authorities;
};

struct MonadChain : Chain
{
    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual monad_revision get_monad_revision(uint64_t timestamp) const = 0;

    virtual Result<void> validate_transaction(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        Address const &sender, State &, uint256_t const &base_fee_per_gas,
        std::vector<std::optional<Address>> const &authorities) const override;

    bool revert_transaction(
        uint64_t block_number, uint64_t timestamp, Address const &sender,
        Transaction const &, uint256_t const &base_fee_per_gas, uint64_t i,
        State &, MonadChainContext const &) const;
};

MONAD_NAMESPACE_END
