#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/monad/staking/config.hpp>

#include <utility>

#include <blst.h>
#include <intx/intx.hpp>
#include <secp256k1.h>

MONAD_STAKING_NAMESPACE_BEGIN

namespace test
{
    bool is_secp_secret_valid(bytes32_t const &secret);

    std::pair<blst_p1, blst_scalar>
    gen_bls_keypair(bytes32_t secret = bytes32_t{0x1000});

    std::pair<secp256k1_pubkey, bytes32_t>
    gen_secp_keypair(bytes32_t secret = bytes32_t{0x1000});

    byte_string_fixed<33> serialize_secp_pubkey(secp256k1_pubkey const &);

    byte_string_fixed<64> sign_secp(byte_string_view, bytes32_t const &);

    byte_string_fixed<96> sign_bls(byte_string_view, blst_scalar const &);

    byte_string_fixed<65>
    serialize_secp_pubkey_uncompressed(secp256k1_pubkey const &);

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &, uint256_t const &, uint256_t const &commission = 0,
        bytes32_t secret = bytes32_t{0x1000});

    byte_string craft_undelegate_input(
        u64_be val_id, uint256_t const &amount, uint8_t withdrawal_id);

    byte_string craft_withdraw_input(u64_be val_id, uint8_t withdrawal_id);
}

MONAD_STAKING_NAMESPACE_END
