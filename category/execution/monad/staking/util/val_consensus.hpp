#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>

MONAD_NAMESPACE_BEGIN

///////////////////
// Compact slots //
///////////////////
struct KeysPacked
{
    byte_string_fixed<33> secp_pubkey;
    byte_string_fixed<48> bls_pubkey;
};

static_assert(StorageVariable<KeysPacked>::N == 3);

class State;

class ValConsensus
{
    State &state_;
    Address const &address_;
    uint256_t const key_;

public:
    static_assert(StorageVariable<KeysPacked>::N == 3);

    ValConsensus(State &state, Address const &address, bytes32_t const key);

    /////////////
    // Getters //
    /////////////
    StorageVariable<u256_be> stake() noexcept;
    StorageVariable<u256_be> const stake() const noexcept;
    StorageVariable<KeysPacked> keys() noexcept;
    StorageVariable<KeysPacked> const keys() const noexcept;
};

MONAD_NAMESPACE_END
