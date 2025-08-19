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

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>

#include <evmc/evmc.h>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>
#include <optional>

MONAD_NAMESPACE_BEGIN

enum class TransactionError
{
    Success = 0,
    InsufficientBalance,
    IntrinsicGasGreaterThanLimit,
    BadNonce,
    SenderNotEoa,
    TypeNotSupported,
    MaxFeeLessThanBase,
    PriorityFeeGreaterThanMax,
    NonceExceedsMax,
    InitCodeLimitExceeded,
    GasLimitReached,
    WrongChainId,
    MissingSender,
    GasLimitOverflow,
    InvalidSignature,
    InvalidBlobHash,
};

struct Transaction;

template <evmc_revision rev>
Result<void> static_validate_transaction(
    Transaction const &, std::optional<uint256_t> const &base_fee_per_gas,
    std::optional<uint64_t> const &excess_blob_gas, uint256_t const &chain_id,
    size_t max_code_size);

Result<void> validate_transaction(
    Transaction const &, std::optional<Account> const &sender_account);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::TransactionError>
    : quick_status_code_from_enum_defaults<monad::TransactionError>
{
    static constexpr auto const domain_name = "Transaction Error";
    static constexpr auto const domain_uuid =
        "2f22309f9d7d3e03fbb1eb1ff328da12d290";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
