#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/math.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Helpers for encoding types into solidity encoding ABI. This is both for
// events and so return values from contracts can be parsed by solidity
// `abi.decode()`.

//////////////////////////////////////////////////////////////
// Standalone functions for encoding types.
//
// https://docs.soliditylang.org/en/latest/abi-spec.html#types
//////////////////////////////////////////////////////////////
inline bytes32_t abi_encode_address(Address const &address)
{
    bytes32_t output{};
    std::memcpy(&output.bytes[12], address.bytes, sizeof(Address));
    return output;
}

template <BigEndianType I>
bytes32_t abi_encode_int(I const &i)
{
    static_assert(sizeof(I) <= sizeof(bytes32_t));

    constexpr size_t offset = sizeof(bytes32_t) - sizeof(I);
    bytes32_t output{};
    std::memcpy(&output.bytes[offset], &i, sizeof(I));
    return output;
}

inline byte_string abi_encode_bytes(byte_string_view const input)
{
    byte_string output;
    u256_be const size{input.size()};
    size_t const padding =
        round_up(input.size(), sizeof(bytes32_t)) - input.size();
    output += abi_encode_int(size);
    output += input;
    output = output.append(padding, 0);
    return output;
}

// Encodes a tuple
//  * static types : Have size <= 32 are padded out and added to the "head".
//  * dynamic types: size > 32. The "head" stores the offset in the tail, and
//                   the actual data is stored in the tail.
//
// https://docs.soliditylang.org/en/latest/abi-spec.html#formal-specification-of-the-encoding
class AbiEncoder
{
    byte_string head_;
    byte_string tail_;
    std::vector<std::pair<size_t, size_t>> unresolved_offsets_;

    void add_static(bytes32_t data)
    {
        head_ += data;
    }

    void add_dynamic(byte_string data)
    {
        unresolved_offsets_.emplace_back(head_.size(), tail_.size());
        head_ += bytes32_t{};
        tail_ += data;
    }

public:
    void add_address(Address const &address)
    {
        add_static(abi_encode_address(address));
    }

    template <BigEndianType I>
    void add_int(I const &i)
    {
        add_static(abi_encode_int(i));
    }

    void add_bytes(byte_string_view const data)
    {
        add_dynamic(abi_encode_bytes(data));
    }

    byte_string encode_final()
    {
        for (auto const [unresolved, tail_cumsum] : unresolved_offsets_) {
            u256_be offset = static_cast<uint256_t>(head_.size()) + tail_cumsum;
            uint8_t *const p = &head_[unresolved];
            bytes32_t encoded = abi_encode_int(offset);
            std::memcpy(p, encoded.bytes, sizeof(bytes32_t));
        }

        return std::move(head_) + std::move(tail_);
    }
};

MONAD_NAMESPACE_END
