#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace monad;
using namespace intx::literals;

TEST(AbiEncode, u16)
{
    constexpr uint16_t input{65535};
    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000ffff")
            .value();

    u16_be encoded = input;
    auto const output = byte_string{abi_encode_int(encoded)};
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, u256)
{
    constexpr uint256_t input{15355346523654236542356453_u256};
    byte_string const expected =
        evmc::from_hex(
            "0x0000000000000000000000000000000000000000000cb3"
            "9f00c54ee156444be5")
            .value();

    u256_be encoded = input;
    auto const output = byte_string{abi_encode_int(encoded)};
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, address)
{
    constexpr Address input{0xDEADBEEF000000000000000000F00D0000000100_address};
    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000deadbeef000000000000000000f00d0000000100")
            .value();

    auto const output = byte_string{abi_encode_address(input)};
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, bytes)
{
    byte_string const bls_pubkey = evmc::from_hex(
                                       "0x85686279cefd8ce0d32338910d476ca090b67"
                                       "f97fc6f2fbc7d96b0cf3d7dca2fe9"
                                       "80de55a715702f2ad35ee5f9bd6f9b")
                                       .value();
    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000003085"
            "686279cefd8ce0d32338910d476ca090b67f97fc6f2fbc7d96b0cf3d7dca2fe980"
            "de55a715702f2ad35ee5f9bd6f9b00000000000000000000000000000000")
            .value();

    byte_string const output = abi_encode_bytes(bls_pubkey);
    EXPECT_EQ(output, expected);
}

TEST(AbiEncode, tuple)
{
    byte_string const input_bytes =
        evmc::from_hex(
            "0x85686279cefd8ce0d32338910d476ca090b67245034520354205420354203542"
            "f97fc6f2fbc7d96b0cf3d7dca2f80de55a715702f2ad35ee5f9bd6f9bb")
            .value();
    u256_be const input_u256 = 15324315423000000_u256;

    byte_string const expected =
        evmc::from_hex(
            "000000000000000000000000000000000000000000000000000000000000008000"
            "0000000000000000000000000000000000000000000000003671623936c5c00000"
            "0000000000000000000000000000000000000000000000000000000000e0000000"
            "000000000000000000000000000000000000000000003671623936c5c000000000"
            "0000000000000000000000000000000000000000000000000000003d85686279ce"
            "fd8ce0d32338910d476ca090b67245034520354205420354203542f97fc6f2fbc7"
            "d96b0cf3d7dca2f80de55a715702f2ad35ee5f9bd6f9bb00000000000000000000"
            "0000000000000000000000000000000000000000000000003d85686279cefd8ce0"
            "d32338910d476ca090b67245034520354205420354203542f97fc6f2fbc7d96b0c"
            "f3d7dca2f80de55a715702f2ad35ee5f9bd6f9bb000000")
            .value();
    AbiEncoder encoder;
    encoder.add_bytes(input_bytes);
    encoder.add_int(input_u256);
    encoder.add_bytes(input_bytes);
    encoder.add_int(input_u256);
    auto const output = encoder.encode_final();
    EXPECT_EQ(output, expected);
}
