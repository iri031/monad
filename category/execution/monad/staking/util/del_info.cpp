#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/util/del_info.hpp>

#include <intx/intx.hpp>

#include <cstdlib>

MONAD_NAMESPACE_BEGIN

DelInfo::DelInfo(State &state, Address const &address, bytes32_t const key)
    : state_{state}
    , address_{address}
    , key_{intx::be::load<uint256_t>(key)}
{
}

StorageVariable<u256_be> DelInfo::stake() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_);
}

StorageVariable<u256_be> const DelInfo::stake() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_);
}

StorageVariable<u256_be> DelInfo::acc() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 1);
}

StorageVariable<u256_be> const DelInfo::acc() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 1);
}

StorageVariable<u256_be> DelInfo::rewards() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 2);
}

StorageVariable<u256_be> const DelInfo::rewards() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 2);
}

StorageVariable<u256_be> DelInfo::delta_stake() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 3);
}

StorageVariable<u256_be> const DelInfo::delta_stake() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 3);
}

StorageVariable<u256_be> DelInfo::next_delta_stake() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 4);
}

StorageVariable<u256_be> const DelInfo::next_delta_stake() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 4);
}

StorageVariable<DelInfo::Epochs> DelInfo::epochs() noexcept
{
    return StorageVariable<Epochs>(state_, address_, key_ + 5);
}

StorageVariable<DelInfo::Epochs> const DelInfo::epochs() const noexcept
{
    return StorageVariable<Epochs>(state_, address_, key_ + 5);
}

u64_be DelInfo::get_delta_epoch() const noexcept
{
    return epochs().load().delta_epoch;
}

u64_be DelInfo::get_next_delta_epoch() const noexcept
{
    return epochs().load().next_delta_epoch;
}

void DelInfo::set_delta_epoch(u64_be const delta_epoch) noexcept
{
    auto e = epochs().load();
    e.delta_epoch = delta_epoch;
    epochs().store(e);
}

void DelInfo::set_next_delta_epoch(u64_be const next_delta_epoch) noexcept
{
    auto e = epochs().load();
    e.next_delta_epoch = next_delta_epoch;
    epochs().store(e);
}

uint256_t DelInfo::get_next_epoch_stake() const noexcept
{
    return stake().load().native() + delta_stake().load().native();
}

byte_string DelInfo::abi_encode() const noexcept
{
    AbiEncoder encoder;
    encoder.add_int(stake().load());
    encoder.add_int(acc().load());
    encoder.add_int(rewards().load());
    encoder.add_int(delta_stake().load());
    encoder.add_int(next_delta_stake().load());

    auto const e = epochs().load();
    encoder.add_int(e.delta_epoch);
    encoder.add_int(e.next_delta_epoch);

    return encoder.encode_final();
}

void DelInfo::clear() noexcept
{
    stake().clear();
    acc().clear();
    rewards().clear();
    delta_stake().clear();
    next_delta_stake().clear();
    epochs().clear();
}

MONAD_NAMESPACE_END
