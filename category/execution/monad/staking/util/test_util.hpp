#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

#include <blst.h>
#include <intx/intx.hpp>
#include <secp256k1.h>

namespace monad::staking::test
{
    std::pair<blst_p1, blst_scalar>
    gen_bls_keypair(bytes32_t secret = bytes32_t{0x1000});

    std::pair<secp256k1_pubkey, bytes32_t>
    gen_secp_keypair(bytes32_t secret = bytes32_t{0x1000});

    byte_string_fixed<33> serialize_secp_pubkey(secp256k1_pubkey const &pubkey);

    byte_string_fixed<64>
    sign_secp(byte_string_view const message, bytes32_t const &seckey);

    byte_string_fixed<96>
    sign_bls(byte_string_view const message, blst_scalar const &seckey);

    byte_string_fixed<65>
    serialize_secp_pubkey_uncompressed(secp256k1_pubkey const &pubkey);

    std::tuple<byte_string, byte_string, byte_string, Address>
    craft_add_validator_input_raw(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000});

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000});

    byte_string craft_undelegate_input(
        u64_be const val_id, uint256_t const &amount, u8_be const withdrawal_id);

    byte_string
    craft_withdraw_input(u64_be const val_id, u8_be const withdrawal_id);

    byte_string craft_change_commission_input(
        u64_be const val_id, uint256_t const &commission);
}
