#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/util/val_execution.hpp>

#include <intx/intx.hpp>

#include <cstdlib>

MONAD_NAMESPACE_BEGIN

ValExecution::ValExecution(
    State &state, Address const &address, bytes32_t const key)
    : state_{state}
    , address_{address}
    , key_{intx::be::load<uint256_t>(key)}
{
}

StorageVariable<u256_be> ValExecution::stake() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_);
}

StorageVariable<u256_be> const ValExecution::stake() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_);
}

StorageVariable<u256_be> ValExecution::acc() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 1);
}

StorageVariable<u256_be> const ValExecution::acc() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 1);
}

StorageVariable<u256_be> ValExecution::commission() noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 2);
}

StorageVariable<u256_be> const ValExecution::commission() const noexcept
{
    return StorageVariable<u256_be>(state_, address_, key_ + 2);
}

StorageVariable<KeysPacked> ValExecution::keys() noexcept
{
    return StorageVariable<KeysPacked>{state_, address_, key_ + 3};
}

StorageVariable<KeysPacked> const ValExecution::keys() const noexcept
{
    return StorageVariable<KeysPacked>{state_, address_, key_ + 3};
}

StorageVariable<AddressFlags> ValExecution::address_flags() noexcept
{
    return StorageVariable<AddressFlags>{state_, address_, key_ + 6};
}

StorageVariable<AddressFlags> const ValExecution::address_flags() const noexcept
{
    return StorageVariable<AddressFlags>{state_, address_, key_ + 6};
}

StorageVariable<u256_be> ValExecution::unclaimed_rewards() noexcept
{
    return StorageVariable<u256_be>{state_, address_, key_ + 7};
}

StorageVariable<u256_be> const ValExecution::unclaimed_rewards() const noexcept
{
    return StorageVariable<u256_be>{state_, address_, key_ + 7};
}

byte_string ValExecution::abi_encode() const noexcept
{
    AbiEncoder encoder;
    auto const af = address_flags().load();
    encoder.add_address(af.auth_address);
    encoder.add_int(af.flags);
    encoder.add_int(stake().load());
    encoder.add_int(acc().load());
    encoder.add_int(commission().load());

    auto const k = keys().load();
    encoder.add_bytes(to_byte_string_view(k.secp_pubkey));
    encoder.add_bytes(to_byte_string_view(k.bls_pubkey));

    return encoder.encode_final();
}

Address ValExecution::auth_address() const noexcept
{
    return address_flags().load().auth_address;
}

uint64_t ValExecution::get_flags() const noexcept
{
    return address_flags().load().flags.native();
}

void ValExecution::set_flag(uint64_t const flag) noexcept
{
    auto af = address_flags().load();
    af.flags = af.flags.native() | flag;
    address_flags().store(af);
}

void ValExecution::clear_flag(uint64_t const flag) noexcept
{
    auto af = address_flags().load();
    af.flags = af.flags.native() & ~flag;
    address_flags().store(af);
}

bool ValExecution::exists() const noexcept
{
    return address_flags().load_checked().has_value();
}

MONAD_NAMESPACE_END
