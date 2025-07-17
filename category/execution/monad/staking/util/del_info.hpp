#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>

MONAD_NAMESPACE_BEGIN

class State;

class DelInfo
{
    State &state_;
    Address const &address_;
    uint256_t const key_;

public:
    ///////////////////
    // Compact slots //
    ///////////////////
    struct Epochs
    {
        u64_be delta_epoch;
        u64_be next_delta_epoch;
    };

    static_assert(StorageVariable<Epochs>::N == 1);

    DelInfo(State &state, Address const &address, bytes32_t const key);

    /////////////
    // Getters //
    /////////////
    StorageVariable<u256_be> stake() noexcept;
    StorageVariable<u256_be> const stake() const noexcept;
    StorageVariable<u256_be> acc() noexcept;
    StorageVariable<u256_be> const acc() const noexcept;
    StorageVariable<u256_be> rewards() noexcept;
    StorageVariable<u256_be> const rewards() const noexcept;
    StorageVariable<u256_be> delta_stake() noexcept;
    StorageVariable<u256_be> const delta_stake() const noexcept;
    StorageVariable<u256_be> next_delta_stake() noexcept;
    StorageVariable<u256_be> const next_delta_stake() const noexcept;
    StorageVariable<Epochs> epochs() noexcept;
    StorageVariable<Epochs> const epochs() const noexcept;

    /////////////
    // Helpers //
    /////////////
    u64_be get_delta_epoch() const noexcept;
    u64_be get_next_delta_epoch() const noexcept;
    void set_delta_epoch(u64_be) noexcept;
    void set_next_delta_epoch(u64_be) noexcept;

    uint256_t get_next_epoch_stake() const noexcept;

    byte_string abi_encode() const noexcept;
    void clear() noexcept;
};

MONAD_NAMESPACE_END
