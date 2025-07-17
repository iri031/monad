#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/util/val_consensus.hpp>

#include <intx/intx.hpp>

#include <cstdlib>

MONAD_NAMESPACE_BEGIN

ValConsensus::ValConsensus(
    State &state, Address const &address, bytes32_t const key)
    : state_{state}
    , address_{address}
    , key_{intx::be::load<uint256_t>(key)}
{
}

StorageVariable<u256_be> ValConsensus::stake() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_);
}

StorageVariable<u256_be> const ValConsensus::stake() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_);
}

StorageVariable<KeysPacked> ValConsensus::keys() noexcept
{
    return StorageVariable<KeysPacked>{state_, address_, key_ + 1};
}

StorageVariable<KeysPacked> const ValConsensus::keys() const noexcept
{
    return StorageVariable<KeysPacked>{state_, address_, key_ + 1};
}

MONAD_NAMESPACE_END
