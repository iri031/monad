#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/staking/util/val_consensus.hpp>

MONAD_NAMESPACE_BEGIN

///////////////////
// Compact slots //
///////////////////
struct AddressFlags
{
    Address auth_address;
    u64_be flags;
};

static_assert(StorageVariable<AddressFlags>::N == 1);

class State;

class ValExecution
{
    State &state_;
    Address const &address_;
    uint256_t const key_;

public:
    ValExecution(State &state, Address const &address, bytes32_t const key);

    /////////////
    // Getters //
    /////////////
    StorageVariable<u256_be> stake() noexcept;
    StorageVariable<u256_be> const stake() const noexcept;
    StorageVariable<u256_be> acc() noexcept;
    StorageVariable<u256_be> const acc() const noexcept;
    StorageVariable<u256_be> commission() noexcept;
    StorageVariable<u256_be> const commission() const noexcept;
    StorageVariable<KeysPacked> keys() noexcept;
    StorageVariable<KeysPacked> const keys() const noexcept;
    StorageVariable<AddressFlags> address_flags() noexcept;
    StorageVariable<AddressFlags> const address_flags() const noexcept;
    StorageVariable<u256_be> unclaimed_rewards() noexcept;
    StorageVariable<u256_be> const unclaimed_rewards() const noexcept;

    /////////////
    // Helpers //
    /////////////
    Address auth_address() const noexcept;
    uint64_t get_flags() const noexcept;
    void set_flag(uint64_t) noexcept;
    void clear_flag(uint64_t) noexcept;

    byte_string abi_encode() const noexcept;
    bool exists() const noexcept;
};

MONAD_NAMESPACE_END
