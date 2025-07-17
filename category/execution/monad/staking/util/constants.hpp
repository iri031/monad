#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>

#include <cstdint>
#include <memory>
#include <optional>
#include <span>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

using namespace intx::literals;

inline constexpr uint256_t MON{1000000000000000000_u256};

inline constexpr uint256_t MIN_VALIDATE_STAKE{1'000'000 * MON};
inline constexpr uint256_t ACTIVE_VALIDATOR_STAKE{50'000'000 * MON};
inline constexpr uint256_t REWARD{1 * MON};
inline constexpr uint256_t UNIT_BIAS{100000000000000000000000000000_u256};

inline constexpr Address STAKING_CONTRACT_ADDRESS{0x1000};
inline constexpr uint64_t WITHDRAWAL_DELAY = 1;

enum
{
    ValidatorFlagsOk = 0,
    ValidatorFlagsStakeTooLow = (1 << 0),
    ValidatorFlagWithdrawn = (1 << 1),
    ValidatorFlagsDoubleSign = (1 << 2),
};

MONAD_NAMESPACE_END
