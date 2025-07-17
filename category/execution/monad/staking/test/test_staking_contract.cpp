#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/int_fmt.hpp> // NOLINT
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>
#include <monad/vm/vm.hpp>

#include <test_resource_data.h>

#include <cstdint>
#include <memory>
#include <utility>

#include <blst.h>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <secp256k1.h>

using namespace monad;
using namespace monad::test;

namespace
{

    std::unique_ptr<secp256k1_context, decltype(&secp256k1_context_destroy)>
        secp_context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            secp256k1_context_destroy);

    std::pair<blst_p1, blst_scalar>
    gen_bls_keypair(bytes32_t secret = bytes32_t{0x1000})
    {
        blst_scalar secret_key;
        blst_p1 public_key;

        blst_keygen(&secret_key, secret.bytes, sizeof(secret));
        blst_sk_to_pk_in_g1(&public_key, &secret_key);
        return {public_key, secret_key};
    }

    std::pair<secp256k1_pubkey, bytes32_t>
    gen_secp_keypair(bytes32_t secret = bytes32_t{0x1000})
    {
        secp256k1_pubkey public_key;

        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_create(
                     secp_context.get(), &public_key, secret.bytes));

        return {public_key, secret};
    }

    byte_string_fixed<33> serialize_secp_pubkey(secp256k1_pubkey const &pubkey)
    {
        byte_string_fixed<33> secp_pubkey_serialized;
        size_t size = 33;
        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_serialize(
                     secp_context.get(),
                     secp_pubkey_serialized.data(),
                     &size,
                     &pubkey,
                     SECP256K1_EC_COMPRESSED));
        MONAD_ASSERT(size == 33);
        return secp_pubkey_serialized;
    }

    byte_string_fixed<64>
    sign_secp(byte_string_view const message, bytes32_t const &seckey)
    {
        secp256k1_ecdsa_signature sig;
        auto const digest = blake3(message);
        MONAD_ASSERT(
            1 == secp256k1_ecdsa_sign(
                     secp_context.get(),
                     &sig,
                     digest.bytes,
                     seckey.bytes,
                     secp256k1_nonce_function_default,
                     NULL));

        byte_string_fixed<64> serialized;
        MONAD_ASSERT(
            1 == secp256k1_ecdsa_signature_serialize_compact(
                     secp_context.get(), serialized.data(), &sig));
        return serialized;
    }

    byte_string_fixed<96>
    sign_bls(byte_string_view const message, blst_scalar const &seckey)
    {
        static constexpr char DST[] =
            "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
        blst_p2 hash;
        blst_hash_to_g2(
            &hash,
            message.data(),
            message.size(),
            reinterpret_cast<uint8_t const *>(DST),
            sizeof(DST) - 1,
            nullptr,
            0);
        blst_p2 sig;
        blst_sign_pk_in_g1(&sig, &hash, &seckey);

        byte_string_fixed<96> serialized;
        blst_p2_compress(serialized.data(), &sig);
        return serialized;
    }

    byte_string_fixed<65>
    serialize_secp_pubkey_uncompressed(secp256k1_pubkey const &pubkey)
    {
        byte_string_fixed<65> secp_pubkey_serialized;
        size_t size = 65;
        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_serialize(
                     secp_context.get(),
                     secp_pubkey_serialized.data(),
                     &size,
                     &pubkey,
                     SECP256K1_EC_UNCOMPRESSED));
        MONAD_ASSERT(size == 65);
        return secp_pubkey_serialized;
    }

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000})
    {
        auto const [bls_pubkey, bls_seckey] = gen_bls_keypair(secret);
        auto const [secp_pubkey, secp_seckey] = gen_secp_keypair(secret);

        auto const secp_pubkey_serialized = serialize_secp_pubkey(secp_pubkey);
        auto const bls_pubkey_serialized = [&bls_pubkey] {
            byte_string_fixed<48> serialized;
            blst_p1_compress(serialized.data(), &bls_pubkey);
            return serialized;
        }();

        auto const address = address_from_secpkey(
            serialize_secp_pubkey_uncompressed(secp_pubkey));
        // fmt::println("My value: {}", address);

        byte_string input;
        input += to_byte_string_view(secp_pubkey_serialized);
        input += to_byte_string_view(bls_pubkey_serialized);
        input += to_byte_string_view(auth_address.bytes);
        input += to_byte_string_view(intx::be::store<bytes32_t>(stake).bytes);
        input += to_byte_string_view(u256_be{commission}.bytes);

        // sign with both keys
        byte_string_view const message = input;
        auto const secp_sig_serialized = sign_secp(message, secp_seckey);
        auto const bls_sig_serialized = sign_bls(message, bls_seckey);

        input += to_byte_string_view(secp_sig_serialized);
        input += to_byte_string_view(bls_sig_serialized);

        return {input, address};
    }

    byte_string craft_undelegate_input(
        u64_be const val_id, uint256_t const &amount,
        uint8_t const withdrawal_id)
    {
        u256_be const value{amount};

        byte_string input;
        input += to_byte_string_view(val_id.bytes);
        input += to_byte_string_view(value.bytes);
        input += withdrawal_id;
        return input;
    }

    byte_string
    craft_withdraw_input(u64_be const val_id, uint8_t const withdrawal_id)
    {
        byte_string input;
        input += to_byte_string_view(val_id.bytes);
        input += withdrawal_id;
        return input;
    }
}

struct Stake : public ::testing::Test
{
    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    StakingContract contract{state, STAKING_CONTRACT_ADDRESS};

    void SetUp() override
    {
        commit_sequential(
            tdb,
            StateDeltas{
                {STAKING_CONTRACT_ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 0, .nonce = 1}}}}},
            Code{},
            BlockHeader{});
        state.touch(STAKING_CONTRACT_ADDRESS);
        u64_be start_epoch{1};
        contract.vars.epoch.store(start_epoch);
    }

    void post_call(StakingContract::Status status)
    {
        if (status == StakingContract::SUCCESS) {
            state.pop_accept();
        }
        else {
            state.pop_reject();
        }
    }

    void inc_epoch()
    {
        uint64_t const next_epoch = contract.vars.epoch.load().native() + 1;
        syscall_on_epoch_change(next_epoch);
    }

    void skip_to_next_epoch()
    {
        syscall_snapshot();
        inc_epoch();
    }

    void touch_delegator(u64_be const val_id, Address const &address)
    {
        byte_string input;
        input += to_byte_string_view(val_id.bytes);
        input += to_byte_string_view(address.bytes);
        (void)contract.precompile_get_delegator(input, address, {});
    }

    struct ValResult
    {
        StakingContract::Status status;
        u64_be id;
        Address sign_address;
    };

    void check_delegator_c_state(
        ValResult const &val, Address const &delegator,
        uint256_t expected_stake, uint256_t expected_rewards)
    {
        auto const del = contract.vars.delegator(val.id, delegator);
        touch_delegator(val.id, delegator);

        EXPECT_EQ(del.stake().load().native(), expected_stake);
        EXPECT_EQ(del.rewards().load().native(), expected_rewards);
    }

    void check_delegator_zero(u64_be const val_id, Address const &delegator)
    {
        auto const del = contract.vars.delegator(val_id, delegator);
        touch_delegator(val_id, delegator);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.acc().load().native(), 0);
        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch(), 0);
        EXPECT_EQ(del.get_next_delta_epoch(), 0);
    }

    StakingContract::Status syscall_snapshot()
    {
        return contract.syscall_snapshot({}, {}, {}).status;
    }

    StakingContract::Status syscall_on_epoch_change(uint64_t const epoch)
    {
        u64_be const epoch_encoded = epoch;
        byte_string_view input{epoch_encoded.bytes, sizeof(epoch_encoded)};
        return contract.syscall_on_epoch_change(input, {}, {}).status;
    }

    StakingContract::Status syscall_reward(Address const &address)
    {
        byte_string_view input{address.bytes, sizeof(Address)};
        return contract.syscall_reward(input, {}, {}).status;
    }

    ValResult add_validator(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0,
        bytes32_t const &secret = bytes32_t{0x1000})
    {
        auto const [input, sign_address] =
            craft_add_validator_input(auth_address, stake, commission, secret);
        auto const msg_value = intx::be::store<evmc_uint256be>(stake);
        state.push();
        auto const res =
            contract.precompile_add_validator(input, auth_address, msg_value);
        post_call(res.status);
        u64_be val_id = 0;
        if (res.status == StakingContract::SUCCESS) {
            state.add_to_balance(STAKING_CONTRACT_ADDRESS, stake);
            std::memcpy(val_id.bytes, res.data.data() + 24, 8);
        }
        return ValResult{
            .status = res.status, .id = val_id, .sign_address = sign_address};
    }

    StakingContract::Status delegate(
        u64_be const val_id, Address const &del_address, uint256_t const &stake)
    {
        auto const input = to_byte_string_view(val_id.bytes);
        auto const msg_value = intx::be::store<evmc_uint256be>(stake);
        state.push();
        auto const status =
            contract.precompile_delegate(input, del_address, msg_value).status;
        post_call(status);
        if (status == StakingContract::SUCCESS) {
            state.add_to_balance(STAKING_CONTRACT_ADDRESS, stake);
        }
        return status;
    }

    StakingContract::Status undelegate(
        u64_be const val_id, Address const &address,
        uint8_t const withdrawal_id, uint256_t const &amount)
    {
        auto const input =
            craft_undelegate_input(val_id, amount, withdrawal_id);
        state.push();
        auto const status =
            contract.precompile_undelegate(input, address, {}).status;
        post_call(status);
        return status;
    }

    StakingContract::Status withdraw(
        u64_be const val_id, Address const &address,
        uint8_t const withdrawal_id)
    {
        auto const input = craft_withdraw_input(val_id, withdrawal_id);
        state.push();
        auto const status =
            contract.precompile_withdraw(input, address, {}).status;
        post_call(status);
        return status;
    }

    StakingContract::Status
    compound(u64_be const val_id, Address const &address)
    {
        auto const input = to_byte_string_view(val_id.bytes);
        state.push();
        auto const status =
            contract.precompile_compound(input, address, {}).status;
        post_call(status);
        return status;
    }

    StakingContract::Status
    claim_rewards(u64_be const val_id, Address const &address)
    {
        auto const input = to_byte_string_view(val_id.bytes);
        state.push();
        auto const status =
            contract.precompile_claim_rewards(input, address, {}).status;
        post_call(status);
        return status;
    }

    uint256_t get_balance(Address const &account)
    {
        return intx::be::load<uint256_t>(state.get_balance(account));
    }
};

TEST_F(Stake, invoke_fallback)
{
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);

    byte_string_fixed<8> const signature_bytes = {0xff, 0xff, 0xff, 0xff};
    auto signature = to_byte_string_view(signature_bytes);
    auto const [func, cost] = contract.precompile_dispatch(signature);
    EXPECT_EQ(cost, 0);

    auto const res = (contract.*func)(byte_string_view{}, sender, value);
    EXPECT_EQ(res.status, StakingContract::METHOD_NOT_SUPPORTED);
}

// Check that accumulator is monotonically increasing - Done
// Check that accumulator is updating principle + reward amount correctly
TEST_F(Stake, accumulator_is_monotonic_again)
{
    // Add validator
    auto const val = add_validator(0xdeadbeef_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    // Loop: call syscall_reward multiple times and test monotonicity
    uint256_t previous_accumulator = 0;

    auto validator1 = contract.vars.val_execution(val.id);

    ASSERT_TRUE(validator1.exists());

    skip_to_next_epoch();

    fmt::println(
        "Initial Balance {} - accumulator: {}",
        intx::to_string(validator1.stake().load().native(), 10),
        intx::to_string(validator1.acc().load().native(), 10));

    constexpr size_t NUM_ITERATIONS = 10;
    for (size_t i = 0; i < NUM_ITERATIONS; ++i) {
        EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
        auto validator = contract.vars.val_execution(val.id);
        auto current_accumulator = validator.acc().load().native();
        fmt::println(
            "Iteration {} - accumulator: {}",
            i,
            intx::to_string(current_accumulator, 10));
        fmt::println(
            "curr Balance {}",
            intx::to_string(validator.stake().load().native(), 10));

        // Check that accumulator is monotonically increasing
        ASSERT_GE(current_accumulator, previous_accumulator);

        // Update for next iteration
        previous_accumulator = current_accumulator;
    }

    skip_to_next_epoch();

    auto const validator = contract.vars.val_execution(val.id);

    ASSERT_TRUE(validator.exists());

    fmt::println(
        "Terminal Balance {} - accumulator: {}",
        intx::to_string(validator.stake().load().native(), 10),
        intx::to_string(validator.acc().load().native(), 10));
}

class StakeCommission
    : public Stake
    , public ::testing::WithParamInterface<uint64_t>
{
};

INSTANTIATE_TEST_SUITE_P(
    Rate, StakeCommission, ::testing::Values(1, 5, 10, 25, 50, 66, 75, 90),
    [](::testing::TestParamInfo<uint64_t> const &info) {
        return std::to_string(info.param);
    });

TEST_P(StakeCommission, validator_has_commission)
{
    auto const commission_percent = GetParam();
    auto const commission =
        (1000000000000000000_u256 * commission_percent) / 100;
    auto const auth_address = 0xababab_address;

    auto const val =
        add_validator(auth_address, ACTIVE_VALIDATOR_STAKE, commission);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();
    auto const del_address = 0xaaaabbbb_address;
    EXPECT_EQ(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, del_address);

    auto const expected_commission = (REWARD * commission_percent) / 100;
    auto const expected_delegator_reward = (REWARD - expected_commission) / 2;
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        expected_delegator_reward);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        expected_commission + expected_delegator_reward);
}

/////////////////////
// add_validator unit tests
/////////////////////

TEST_F(Stake, add_validator_revert_invalid_input_size)
{
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);

    byte_string_view too_short{};
    auto res = contract.precompile_add_validator(too_short, sender, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);

    byte_string too_long(2000, 0xa);
    res = contract.precompile_add_validator(too_short, sender, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);
}

TEST_F(Stake, add_validator_revert_bad_signature)
{
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, MIN_VALIDATE_STAKE);
    auto const message = input.substr(0, 165);

    auto const good_secp_keys = gen_secp_keypair();
    auto const bad_secp_keys = gen_secp_keypair(bytes32_t{0x2000});
    auto const good_bls_keys = gen_bls_keypair();
    auto const bad_bls_keys = gen_bls_keypair(bytes32_t{0x2000});

    // bad secp signature
    {
        byte_string input;
        input += message;
        input += to_byte_string_view(sign_secp(message, bad_secp_keys.second));
        input += to_byte_string_view(sign_bls(message, good_bls_keys.second));
        auto res = contract.precompile_add_validator(input, address, value);
        EXPECT_EQ(
            res.status, StakingContract::SECP_SIGNATURE_VERIFICATION_FAILED);
    }

    // bad bls signature
    {
        byte_string input;
        input += message;
        input += to_byte_string_view(sign_secp(message, good_secp_keys.second));
        input += to_byte_string_view(sign_bls(message, bad_bls_keys.second));
        auto res = contract.precompile_add_validator(input, address, value);
        EXPECT_EQ(
            res.status, StakingContract::BLS_SIGNATURE_VERIFICATION_FAILED);
    }
}

TEST_F(Stake, add_validator_revert_msg_value_not_signed)
{
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, 2 * MIN_VALIDATE_STAKE);
    auto const res = contract.precompile_add_validator(input, address, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);
}

TEST_F(Stake, add_validator_revert_already_exists)
{
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.precompile_add_validator(input, address, value).status,
        StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.precompile_add_validator(input, address, value).status,
        StakingContract::VALIDATOR_EXISTS);
}

TEST_F(Stake, add_validator_revert_minimum_stake_not_met)
{
    auto const value = intx::be::store<evmc_uint256be>(uint256_t{1});
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, uint256_t{1});
    auto const res = contract.precompile_add_validator(input, address, value);
    EXPECT_EQ(res.status, StakingContract::INSUFFICIENT_STAKE);
}

TEST_F(Stake, add_validator_revert_commission_too_high)
{
    constexpr auto commission = 2000000000000000000_u256;
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);
    auto const [input, address] = craft_add_validator_input(
        0xababab_address, MIN_VALIDATE_STAKE, commission);
    auto const res = contract.precompile_add_validator(input, address, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);
}

TEST_F(Stake, add_validator_sufficent_balance)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 = add_validator(
        auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    syscall_snapshot();

    ValResult val2 = {};

    val2 = add_validator(
        other_address,
        ACTIVE_VALIDATOR_STAKE,
        0 /* commission */,
        bytes32_t{0x1001});

    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    inc_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val1.sign_address));

    EXPECT_EQ(contract.vars.valset_consensus().length(), 1);

    EXPECT_EQ(contract.vars.val_execution(1).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(contract.vars.val_execution(2).get_flags(), ValidatorFlagsOk);

    skip_to_next_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val2.sign_address));

    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);

    EXPECT_EQ(contract.vars.val_execution(1).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(contract.vars.val_execution(2).get_flags(), ValidatorFlagsOk);

    EXPECT_EQ(
        contract.vars.val_consensus(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(
        contract.vars.val_consensus(2).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);

    EXPECT_EQ(
        contract.vars.val_execution(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(2).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.val_execution(1).commission().load().native(), 0);
    EXPECT_EQ(contract.vars.val_execution(2).commission().load().native(), 0);
}

TEST_F(Stake, add_validator_insufficent_balance)
{
    auto const auth_address = 0xdeadbeef_address;

    auto const val1 = add_validator(
        auth_address,
        MIN_VALIDATE_STAKE,
        1 /* commission */,
        bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    syscall_snapshot();
    ValResult val2 = {};
    val2 = add_validator(
        auth_address,
        ACTIVE_VALIDATOR_STAKE - 1,
        2 /* commission */,
        bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    inc_epoch();

    EXPECT_EQ(
        StakingContract::BLOCK_AUTHOR_NOT_IN_SET,
        syscall_reward(val1.sign_address));

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);
    EXPECT_EQ(
        contract.vars.val_execution(1).get_flags(), ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(2).get_flags(), ValidatorFlagsStakeTooLow);

    skip_to_next_epoch();

    EXPECT_EQ(
        StakingContract::BLOCK_AUTHOR_NOT_IN_SET,
        syscall_reward(val2.sign_address));

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);

    EXPECT_EQ(
        contract.vars.val_execution(1).get_flags(), ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(2).get_flags(), ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(1).stake().load().native(),
        MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(2).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE - 1);
    EXPECT_EQ(contract.vars.val_execution(1).commission().load().native(), 1);
    EXPECT_EQ(contract.vars.val_execution(2).commission().load().native(), 2);
}

/////////////////////
// validator tests
/////////////////////

TEST_F(Stake, validator_delegate_before_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    ValResult val2 = {};

    val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});

    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();

    // check val info
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);

    // check del
    check_delegator_c_state(
        val1, auth_address, ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE, 0);
    check_delegator_c_state(val2, auth_address, ACTIVE_VALIDATOR_STAKE, 0);
    check_delegator_c_state(val2, other_address, MIN_VALIDATE_STAKE, 0);
}

TEST_F(Stake, validator_undelegate_before_delegator_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, 50),
        StakingContract::INSUFFICIENT_STAKE);

    syscall_snapshot();

    ValResult val2 = {};

    val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});

    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, 50),
        StakingContract::INSUFFICIENT_STAKE);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, 50), StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, 50), StakingContract::SUCCESS);
}

TEST_F(Stake, validator_compound_before_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(compound(val1.id, auth_address), StakingContract::SUCCESS);

    syscall_snapshot();

    ValResult val2 = {};

    val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});

    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(compound(val2.id, auth_address), StakingContract::SUCCESS);

    inc_epoch();

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).stake().load().native(),
        MIN_VALIDATE_STAKE + MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);

    check_delegator_c_state(
        val1, auth_address, MIN_VALIDATE_STAKE + MIN_VALIDATE_STAKE, 0);
    check_delegator_c_state(val2, auth_address, ACTIVE_VALIDATOR_STAKE, 0);
    check_delegator_c_state(val2, other_address, MIN_VALIDATE_STAKE, 0);
}

TEST_F(Stake, validator_withdrawal_before_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id),
        StakingContract::UNKNOWN_WITHDRAWAL_ID);

    syscall_snapshot();

    ValResult val2 = {};

    val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});

    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        withdraw(val2.id, auth_address, withdrawal_id),
        StakingContract::UNKNOWN_WITHDRAWAL_ID);

    inc_epoch();
    skip_to_next_epoch();

    // check validator info
    // check delegator info
    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id),
        StakingContract::UNKNOWN_WITHDRAWAL_ID);
    EXPECT_EQ(
        withdraw(val2.id, auth_address, withdrawal_id),
        StakingContract::UNKNOWN_WITHDRAWAL_ID);
}

TEST_F(Stake, validator_activation_via_delegate)
{
    auto const auth_address = 0xdeadbeef_address;

    // create, minimum amount of stake to be a validator, but less than the
    // amount required to be put in the valset.
    auto const val = add_validator(auth_address, MIN_VALIDATE_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    skip_to_next_epoch();
    EXPECT_TRUE(contract.vars.valset_consensus().empty());

    // a delegator stakes enough to activate the validator
    EXPECT_EQ(
        delegate(val.id, 0xabab_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(), ValidatorFlagsOk);
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.valset_consensus().length(), 1);

    // undelegate, once again deactivating this validator
    EXPECT_EQ(
        undelegate(val.id, 0xabab_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    skip_to_next_epoch();
    EXPECT_TRUE(contract.vars.valset_consensus().empty());
}

TEST_F(Stake, validator_multiple_delegations)
{ // epoch 1
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    // epoch 2
    skip_to_next_epoch();
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, REWARD);

    for (uint32_t i = 0; i < 1; ++i) {
        EXPECT_EQ(
            delegate(val.id, auth_address, MIN_VALIDATE_STAKE),
            StakingContract::SUCCESS);
    }

    syscall_snapshot();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, 2 * REWARD);

    EXPECT_EQ(
        delegate(val.id, auth_address, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    // epoch 3
    inc_epoch();

    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE,
        2 * REWARD);
    // epoch 4
    skip_to_next_epoch();
    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + 2 * MIN_VALIDATE_STAKE,
        2 * REWARD);
}

// compound a validator before and after snapshot
TEST_F(Stake, validator_compound)
{ // epoch 1
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    // epoch 2
    skip_to_next_epoch();
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, REWARD);

    for (uint32_t i = 0; i < 1; ++i) {
        EXPECT_EQ(compound(val.id, auth_address), StakingContract::SUCCESS);
    }

    syscall_snapshot();
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, REWARD);

    EXPECT_EQ(compound(val.id, auth_address), StakingContract::SUCCESS);

    // epoch 3
    inc_epoch();

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + REWARD, 0);
    // epoch 4
    skip_to_next_epoch();
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + 2 * REWARD, 0);
}

TEST_F(Stake, validator_undelegate)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    ValResult val2 = {};

    val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});

    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val1.id, auth_address, 2, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 2, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        withdraw(val2.id, auth_address, withdrawal_id),
        StakingContract::SUCCESS);

    // check val info
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);
    EXPECT_EQ(contract.vars.val_execution(val1.id).stake().load().native(), 0);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).stake().load().native(),
        MIN_VALIDATE_STAKE);

    // check del
    check_delegator_c_state(val1, auth_address, 0, 0);
    check_delegator_c_state(val2, auth_address, 0, 0);
    check_delegator_c_state(val2, other_address, MIN_VALIDATE_STAKE, 0);
}

TEST_F(Stake, validator_exit_via_validator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        undelegate(
            val1.id,
            auth_address,
            1,
            ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, other_address, 1, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(
            val1.id,
            auth_address,
            ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 1);

    EXPECT_EQ(
        delegate(val2.id, other_address, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);
    skip_to_next_epoch();

    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        withdraw(val2.id, other_address, withdrawal_id),
        StakingContract::SUCCESS);
}

TEST_F(Stake, validator_exit_via_delegator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 1);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);
    skip_to_next_epoch();

    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        withdraw(val2.id, auth_address, withdrawal_id),
        StakingContract::SUCCESS);
}

TEST_F(Stake, validator_exit_multiple_delegations)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    EXPECT_EQ(get_balance(auth_address), 0);

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val1.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val2.sign_address), StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(
            val1.id,
            auth_address,
            ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(
        delegate(
            val2.id,
            auth_address,
            ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(claim_rewards(val2.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(withdraw(val2.id, auth_address, 1), StakingContract::SUCCESS);
    EXPECT_EQ(
        get_balance(auth_address), ACTIVE_VALIDATOR_STAKE + 980392156862745098);

    EXPECT_EQ(claim_rewards(val2.id, other_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(other_address), 19607843137254901);

    EXPECT_EQ(claim_rewards(val1.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val1.id, auth_address, 1), StakingContract::SUCCESS);
    EXPECT_EQ(
        get_balance(auth_address),
        ACTIVE_VALIDATOR_STAKE + (REWARD - 1) + ACTIVE_VALIDATOR_STAKE +
            980392156862745098);
}

TEST_F(Stake, validator_exit_multiple_delegations_full_withdrawal)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    EXPECT_EQ(get_balance(auth_address), 0);

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(syscall_reward(val1.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val2.sign_address), StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(
            val1.id,
            auth_address,
            ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(
        delegate(
            val2.id,
            auth_address,
            ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(claim_rewards(val2.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val2.id, auth_address, 1), StakingContract::SUCCESS);
    EXPECT_EQ(
        get_balance(auth_address), ACTIVE_VALIDATOR_STAKE + 980392156862745098);

    EXPECT_EQ(claim_rewards(val2.id, other_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(other_address), 19607843137254901);

    EXPECT_EQ(claim_rewards(val1.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val1.id, auth_address, 1), StakingContract::SUCCESS);
    EXPECT_EQ(
        get_balance(auth_address),
        ACTIVE_VALIDATOR_STAKE + (REWARD - 1) + ACTIVE_VALIDATOR_STAKE +
            980392156862745098);

    check_delegator_c_state(val1, auth_address, ACTIVE_VALIDATOR_STAKE - 1, 0);
    check_delegator_c_state(
        val2, auth_address, ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1, 0);
    check_delegator_c_state(val2, other_address, MIN_VALIDATE_STAKE, 0);

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE - 1),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(
            val2.id,
            auth_address,
            1,
            ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1),
        StakingContract::SUCCESS);

    skip_to_next_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(claim_rewards(val2.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val2.id, auth_address, 1), StakingContract::SUCCESS);

    EXPECT_EQ(claim_rewards(val2.id, other_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(other_address), 19607843137254901);

    EXPECT_EQ(claim_rewards(val1.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val1.id, auth_address, 1), StakingContract::SUCCESS);
    EXPECT_EQ(
        get_balance(auth_address),
        ACTIVE_VALIDATOR_STAKE + (REWARD - 1) + ACTIVE_VALIDATOR_STAKE +
            980392156862745098 + ACTIVE_VALIDATOR_STAKE - 1 +
            ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1);
}

TEST_F(Stake, validator_exit_claim_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(syscall_reward(val1.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val2.sign_address), StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(claim_rewards(val1.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), REWARD - 1);
    EXPECT_EQ(claim_rewards(val2.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), 980392156862745098 + (REWARD - 1));

    EXPECT_EQ(get_balance(other_address), 0);
    EXPECT_EQ(claim_rewards(val2.id, other_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(other_address), 19607843137254901);
}

TEST_F(Stake, validator_exit_compound)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(syscall_reward(val1.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val2.sign_address), StakingContract::SUCCESS);

    EXPECT_EQ(compound(val1.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(compound(val2.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(compound(val2.id, other_address), StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);
    EXPECT_EQ(claim_rewards(val1.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(claim_rewards(val2.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(claim_rewards(val2.id, other_address), StakingContract::SUCCESS);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(get_balance(other_address), 0);

    check_delegator_c_state(
        val2, other_address, MIN_VALIDATE_STAKE + 19607843137254901, 0);

    check_delegator_c_state(val2, auth_address, 980392156862745098, 0);

    check_delegator_c_state(
        val1, auth_address, MIN_VALIDATE_STAKE + REWARD - 1, 0);
}

TEST_F(Stake, validator_removes_self)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, MIN_VALIDATE_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, 0xabab_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();

    uint8_t withdrawal_id{1};
    EXPECT_EQ(
        undelegate(val.id, auth_address, withdrawal_id, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    // check execution state
    auto const val_execution = contract.vars.val_execution(val.id);
    EXPECT_EQ(val_execution.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
    // despite having enough stake to be active, the primary validator has
    // withdrawn, rendering the validator inactive
    EXPECT_TRUE(val_execution.get_flags() & ValidatorFlagWithdrawn);

    // validator can still be rewarded this epoch because he's active
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // take snapshot
    syscall_snapshot();

    // execution view and consensus view should both show validator removed
    EXPECT_EQ(contract.vars._valset_consensus().length(), 0);
    // validate snapshot view since the current epoch is ongoing.
    EXPECT_EQ(contract.vars._valset_snapshot().length(), 1);
    auto const val_snapshot = contract.vars._val_snapshot(val.id);
    EXPECT_EQ(
        val_snapshot.stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);

    // rewards now reference the snapshot set and should continue to work
    // for this validator
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    inc_epoch();

    // consensus view doesn't include this validator, and reward fails
    EXPECT_EQ(
        syscall_reward(val.sign_address),
        StakingContract::BLOCK_AUTHOR_NOT_IN_SET);
}

TEST_F(Stake, validator_constant_validator_set)
{

    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    syscall_snapshot();

    auto const val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    uint8_t withdrawal_id{1};

    for (int i = 0; i < 10; ++i) {
        EXPECT_EQ(
            undelegate(
                val1.id, auth_address, withdrawal_id, MIN_VALIDATE_STAKE + 1),
            StakingContract::SUCCESS);

        EXPECT_EQ(
            undelegate(
                val2.id, auth_address, withdrawal_id, MIN_VALIDATE_STAKE + 1),
            StakingContract::SUCCESS);

        EXPECT_EQ(
            delegate(val1.id, auth_address, MIN_VALIDATE_STAKE + 1),
            StakingContract::SUCCESS);

        EXPECT_EQ(
            delegate(val2.id, auth_address, MIN_VALIDATE_STAKE + 1),
            StakingContract::SUCCESS);

        ++withdrawal_id;
    }

    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 2);
}

TEST_F(Stake, validator_joining_boundary_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val1 = add_validator(
        auth_address,
        ACTIVE_VALIDATOR_STAKE,
        0 /* commission */,
        bytes32_t{0x1000});
    ValResult val2 = {};
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    // add a new validator before adding the snapshot. simulate the case
    // when a malicous consensus client rewards themselves early. all other
    // nodes will not reward him, indicated by the BLOCK_AUTHOR_NOT_IN_SET
    // error code, producing a state root mismatch on that block.
    syscall_snapshot();
    unsigned DELAY_WINDOW = 6000;
    for (unsigned i = 0; i < DELAY_WINDOW; ++i) {
        EXPECT_EQ(
            StakingContract::BLOCK_AUTHOR_NOT_IN_SET,
            syscall_reward(val1.sign_address));

        if (i == (DELAY_WINDOW - 100)) {
            val2 = add_validator(
                auth_address,
                ACTIVE_VALIDATOR_STAKE,
                0 /* commission */,
                bytes32_t{0x1001});
            EXPECT_EQ(val2.status, StakingContract::SUCCESS);
        }
    }

    // joined after the boundary, not active
    EXPECT_EQ(
        StakingContract::BLOCK_AUTHOR_NOT_IN_SET,
        syscall_reward(val2.sign_address));
    inc_epoch();

    // joined before the boundary, now active
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val1.sign_address));
}

// consensus misses a snapshot, validator cant join
TEST_F(Stake, validator_miss_snapshot_miss_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val1 = add_validator(
        auth_address,
        ACTIVE_VALIDATOR_STAKE,
        0 /* commission */,
        bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    inc_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 0);
    EXPECT_EQ(contract.vars.val_execution(1).get_flags(), ValidatorFlagsOk);

    EXPECT_EQ(
        contract.vars.val_execution(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.val_execution(1).commission().load().native(), 0);
}

// consensus misses a snapshot, validator cant leave
TEST_F(Stake, validator_miss_snapshot_miss_deactivation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val1 = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);
    skip_to_next_epoch();

    EXPECT_EQ(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();

    EXPECT_EQ(contract.vars.valset_consensus().length(), 1);
    EXPECT_EQ(
        contract.vars.val_execution(1).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);

    EXPECT_EQ(
        contract.vars.val_consensus(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.val_execution(1).stake().load().native(), 0);
}

TEST_F(Stake, validator_handle_multiple_snapshots)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val1 = add_validator(
        auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);
    syscall_snapshot();
    syscall_snapshot();

    inc_epoch();
}

/////////////////////
// delegate tests
/////////////////////

TEST_F(Stake, delegator_none_init)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const delegator = 1337_address;

    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    // 1. call get_delegator_info()
    check_delegator_zero(val.id, delegator);

    // 2. undelegate
    EXPECT_EQ(
        undelegate(val.id, delegator, 1, 100),
        StakingContract::INSUFFICIENT_STAKE);
    check_delegator_zero(val.id, delegator);

    EXPECT_EQ(undelegate(val.id, delegator, 1, 0), StakingContract::SUCCESS);
    check_delegator_zero(val.id, delegator);

    // 3. withdraw
    EXPECT_EQ(
        withdraw(val.id, delegator, 1), StakingContract::UNKNOWN_WITHDRAWAL_ID);
    check_delegator_zero(val.id, delegator);

    // 4. compound
    EXPECT_EQ(compound(val.id, delegator), StakingContract::SUCCESS);
    check_delegator_zero(val.id, delegator);

    // 5. claim
    EXPECT_EQ(claim_rewards(val.id, delegator), StakingContract::SUCCESS);
    check_delegator_zero(val.id, delegator);
    EXPECT_EQ(get_balance(delegator), 0);
}

TEST_F(Stake, delegate_noop_add_zero_stake)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    auto const d0 = 0xaaaabbbb_address;
    EXPECT_EQ(delegate(val.id, d0, 0), StakingContract::INSUFFICIENT_STAKE);

    skip_to_next_epoch();
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD);
}

TEST_F(Stake, delegate_noop_subsequent_zero_stake)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const d0 = 0xaaaabbbb_address;

    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        2 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    skip_to_next_epoch();

    // reward the validator.
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    // validator should receive all the reward being the only active
    // delegator.
    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD + REWARD / 2);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD + REWARD / 2);

    EXPECT_EQ(delegate(val.id, d0, 0), StakingContract::INSUFFICIENT_STAKE);

    syscall_snapshot();

    EXPECT_EQ(delegate(val.id, d0, 0), StakingContract::INSUFFICIENT_STAKE);

    {
        auto const del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.rewards().load().native(), REWARD + REWARD / 2);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

TEST_F(Stake, delegate_revert_unknown_validator)
{
    auto const d0 = 0xaaaabbbb_address;
    EXPECT_EQ(
        delegate(3, d0, ACTIVE_VALIDATOR_STAKE),
        StakingContract::UNKNOWN_VALIDATOR);
}

TEST_F(Stake, delegate_init)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    syscall_snapshot();
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    inc_epoch();

    skip_to_next_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        REWARD / 3);

    {
        auto const del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto const del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

TEST_F(Stake, delegate_redelegate_before_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 = add_validator(
        auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    EXPECT_EQ(contract.vars.acc(2, val1.id).load().refcount.native(), 1);

    EXPECT_EQ(
        delegate(val1.id, other_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(contract.vars.acc(2, val1.id).load().refcount.native(), 2);

    EXPECT_EQ(
        delegate(val1.id, other_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(contract.vars.acc(2, val1.id).load().refcount.native(), 2);

    syscall_snapshot();

    EXPECT_EQ(
        delegate(val1.id, other_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(contract.vars.acc(3, val1.id).load().refcount.native(), 1);

    EXPECT_EQ(
        delegate(val1.id, other_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    EXPECT_EQ(contract.vars.acc(3, val1.id).load().refcount.native(), 1);

    inc_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val1.sign_address));

    touch_delegator(val1.id, auth_address);
    EXPECT_EQ(contract.vars.acc(2, val1.id).load().refcount.native(), 1);

    touch_delegator(val1.id, other_address);
    EXPECT_EQ(contract.vars.acc(2, val1.id).load().refcount.native(), 0);

    EXPECT_EQ(
        contract.vars.delegator(val1.id, auth_address)
            .rewards()
            .load()
            .native(),
        REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val1.id, other_address)
            .rewards()
            .load()
            .native(),
        2 * REWARD / 3);
    EXPECT_EQ(contract.vars.acc(2, val1.id).load().refcount.native(), 0);

    skip_to_next_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val1.sign_address));
    touch_delegator(val1.id, auth_address);
    touch_delegator(val1.id, other_address);

    EXPECT_EQ(
        contract.vars.delegator(val1.id, auth_address)
            .rewards()
            .load()
            .native(),
        REWARD / 3 + REWARD / 5);
    EXPECT_EQ(
        contract.vars.delegator(val1.id, other_address)
            .rewards()
            .load()
            .native(),
        2 * REWARD / 3 + (4 * REWARD / 5));

    EXPECT_FALSE(contract.vars.acc(2, val1.id).load_checked().has_value());
    EXPECT_FALSE(contract.vars.acc(3, val1.id).load_checked().has_value());
}

TEST_F(Stake, delegate_redelegate_after_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    // reward the validator.
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        0);
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    auto acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    auto acc_boundary = contract.vars.acc(4, val.id).load();
    EXPECT_EQ(acc_boundary.value.native(), 0);
    EXPECT_EQ(acc_boundary.refcount.native(), 1);

    inc_epoch();

    // validator should receive all the reward being the only active
    // delegator.
    touch_delegator(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3);

    // calling touch again should be a no-op
    touch_delegator(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3);

    // secondary delegators were not active and should receive nothing.
    EXPECT_EQ(contract.vars.delegator(val.id, d0).rewards().load().native(), 0);
    EXPECT_EQ(contract.vars.delegator(val.id, d1).rewards().load().native(), 0);

    // reward again with only 1 active delegator
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3 + REWARD / 2);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 2);
    EXPECT_EQ(contract.vars.delegator(val.id, d1).rewards().load().native(), 0);

    skip_to_next_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3 + REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        REWARD / 3);

    acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc_boundary = contract.vars.acc(4, val.id).load();
    EXPECT_EQ(acc_boundary.value.native(), 0);
    EXPECT_EQ(acc_boundary.refcount.native(), 0);

    {
        auto const del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto const del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

TEST_F(Stake, delegate_undelegate_withdraw_redelegate)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    // reward the validator.

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    inc_epoch();

    // reward again with only 1 active delegator
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));

    skip_to_next_epoch();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(val.sign_address));
    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3 + REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        REWARD / 3);

    auto acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    auto acc_boundary = contract.vars.acc(4, val.id).load();
    EXPECT_EQ(acc_boundary.value.native(), 0);
    EXPECT_EQ(acc_boundary.refcount.native(), 0);

    uint8_t const withdrawal_id{1};
    EXPECT_EQ(
        undelegate(val.id, d0, withdrawal_id, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    syscall_snapshot();
    EXPECT_EQ(
        undelegate(val.id, d1, withdrawal_id, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(withdraw(val.id, d0, withdrawal_id), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val.id, d1, withdrawal_id), StakingContract::SUCCESS);

    {
        auto const del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto const del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    {
        auto const del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 8);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto const del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(
            del.next_delta_stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 9);
    }
}

TEST_F(Stake, delegator_delegates_in_boundary)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();

    auto const del_address = 0xaaaabbbb_address;
    EXPECT_EQ(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    // take snapshot and reward during the window. delegator *should not*
    // receive rewards.
    syscall_snapshot();
    unsigned DELAY_WINDOW = 6000;

    for (unsigned i = 0; i < DELAY_WINDOW; ++i) {
        EXPECT_EQ(
            contract.vars.val_consensus(val.id).stake().load().native(),
            ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(
            contract.vars.val_execution(val.id).stake().load().native(),
            ACTIVE_VALIDATOR_STAKE * 2);
        EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    }

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, del_address);

    // validator should get all the rewards since the secondary delegator
    // does not become active in the consensus view until after the window
    // expires.
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * DELAY_WINDOW);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        0);
}

TEST_F(Stake, delegate_redelegation_refcount_before_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    // do a bunch of redelegations before snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_EQ(delegate(val.id, auth_address, 50), StakingContract::SUCCESS);
    }

    syscall_snapshot();

    // and some more in the snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_EQ(delegate(val.id, auth_address, 50), StakingContract::SUCCESS);
    }
    inc_epoch();

    auto acc = contract.vars.acc(2, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    touch_delegator(val.id, auth_address);

    acc = contract.vars.acc(2, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    syscall_snapshot();
    inc_epoch();

    touch_delegator(val.id, auth_address);

    acc = contract.vars.acc(2, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);
}

TEST_F(Stake, delegate_redelegation_refcount_after_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    syscall_snapshot();
    inc_epoch();

    // do a bunch of redelegations before snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_EQ(delegate(val.id, auth_address, 50), StakingContract::SUCCESS);
    }

    syscall_snapshot();

    // and some more in the snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_EQ(delegate(val.id, auth_address, 50), StakingContract::SUCCESS);
    }

    auto acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    acc = contract.vars.acc(4, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    inc_epoch();

    touch_delegator(val.id, auth_address);

    acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.acc(4, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    syscall_snapshot();
    inc_epoch();

    touch_delegator(val.id, auth_address);

    acc = contract.vars.acc(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.acc(4, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);
}

// There are 3 cases for the historic accumulator when a delegator joins a
// validator's stake pool.
// 1. delegators join in same snapshot window as validator
// 2. delegator join in different snapshot window as validator and acc is
// zero
// 3. delegator join in different snapshot window as validator and acc is
// non zero
TEST_F(Stake, delegator_epoch_accumulator_same_snapshot)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    // add 2 delegators in same snapshot window
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    syscall_snapshot();
    inc_epoch();

    // 3 delegators become active. Therefore ref count should be 3 and acc
    // is 0
    EXPECT_EQ(0, contract.vars.acc(u64_be{2}, val.id).load().value.native());
    EXPECT_EQ(3, contract.vars.acc(u64_be{2}, val.id).load().refcount.native());

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    // acc and ref should be empty now
    EXPECT_EQ(0, contract.vars.acc(u64_be{3}, val.id).load().value.native());
    EXPECT_EQ(0, contract.vars.acc(u64_be{3}, val.id).load().refcount.native());
}

TEST_F(Stake, delegator_epoch_accumulator_diff_snapshot)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    syscall_snapshot();
    // add 2 delegators in different snapshot window
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    inc_epoch();

    // 1 delegators become active. Therefore ref count should be 1 and acc
    // is 0
    EXPECT_EQ(0, contract.vars.acc(u64_be{2}, val.id).load().value.native());
    EXPECT_EQ(1, contract.vars.acc(u64_be{2}, val.id).load().refcount.native());

    syscall_snapshot();
    inc_epoch();

    // 2 delegators become active. Therefore ref count should be 2 and acc
    // is 0 since no rewards
    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().value.native(), 0);
    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().refcount.native(), 2);

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    // acc and ref should be empty now for both epochs
    EXPECT_EQ(contract.vars.acc(u64_be{2}, val.id).load().value.native(), 0);
    EXPECT_EQ(contract.vars.acc(u64_be{2}, val.id).load().refcount.native(), 0);

    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().value.native(), 0);
    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().refcount.native(), 0);
}

TEST_F(Stake, delegator_epoch_nz_accumulator_diff_snapshot)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);

    syscall_snapshot();

    // add 2 delegators in different snapshot window
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    inc_epoch();

    // 1 delegators become active. Therefore ref count should be 1 and acc
    // is 0
    EXPECT_EQ(contract.vars.acc(u64_be{2}, val.id).load().value.native(), 0);
    EXPECT_EQ(contract.vars.acc(u64_be{2}, val.id).load().refcount.native(), 1);

    // validator is rewarded. next acc is nonzero.
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    syscall_snapshot();
    inc_epoch();

    // 2 delegators become active. Therefore ref count should be 2 and acc
    // is nonzero
    EXPECT_EQ(
        contract.vars.acc(u64_be{3}, val.id).load().value.native(),
        (REWARD * UNIT_BIAS) / ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().refcount.native(), 2);

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    // acc and ref should be empty now for both epochs
    EXPECT_EQ(contract.vars.acc(u64_be{2}, val.id).load().value.native(), 0);
    EXPECT_EQ(contract.vars.acc(u64_be{2}, val.id).load().refcount.native(), 0);

    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().value.native(), 0);
    EXPECT_EQ(contract.vars.acc(u64_be{3}, val.id).load().refcount.native(), 0);
    {
        auto const del = contract.vars.delegator(val.id, d0);
        EXPECT_GT(del.acc().load().native(), 0);
    }
}

/////////////////////
// compound / redelegate tests
/////////////////////

TEST_F(Stake, delegate_inter_compound_rewards)
{ // epoch 1 - add validator and 2 delegators
    auto const auth_address = 0xdeadbeef_address;
    auto const reward_decimal_rounding = 999999999999999999;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);

    // add 2 delegators
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        2 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    skip_to_next_epoch();
    // epoch 2 - 3 block reward. this should be split evenly.

    // auth account should get 1/3 of all rewards this epoch
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // auth account should get 2/4 rewards at next epoch
    EXPECT_EQ(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    // other delegators should get 1/3 of all rewards this epoch
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        4 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    // decimal inaccuracy. off by 1 wei
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        reward_decimal_rounding);

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    skip_to_next_epoch();
    // epoch 3 - 6 block reward. this should be 1/2 validator, 1/4 to each
    // delegator.

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // delegator rewards should be p*(acc(epoch) - acc(del)) +
    // p + r *(acc(curr) - acc(epoch))

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        2 * reward_decimal_rounding + REWARD / 2 + REWARD);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 4);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 4);
}

TEST_F(Stake, delegate_intra_compound_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const reward_decimal_rounding = 999999999999999999;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);

    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    // add 2 delegators
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        2 * ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        3 * ACTIVE_VALIDATOR_STAKE);

    skip_to_next_epoch();

    // auth account should get 1/3 of all rewards this epoch
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // auth account should get 2/4 rewards at next epoch
    EXPECT_EQ(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    // other delegators should get 1/3 of all rewards this epoch
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        4 * ACTIVE_VALIDATOR_STAKE);

    // decimal inaccuracy. off by 1 wei
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        reward_decimal_rounding);

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // auth account should get 3/5 rewards at next epoch
    // other delegators should get 1/5 of all rewards next epoch
    EXPECT_EQ(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, d0);
    touch_delegator(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        2 * reward_decimal_rounding + 9 * REWARD / 5);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 5);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 5);
}

TEST_F(Stake, delegate_compound_boundary)
{
    // Epoch 1 - Add validator
    auto const auth_address = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(ACTIVE_VALIDATOR_STAKE);
    auto const [input, address] =
        craft_add_validator_input(auth_address, ACTIVE_VALIDATOR_STAKE);
    u64_be const val_id{1};

    // add validator
    EXPECT_EQ(
        contract.precompile_add_validator(input, auth_address, value).status,
        StakingContract::SUCCESS);

    skip_to_next_epoch();

    // Epoch 2 - validator gets reward and compounds it in snapshot
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));
    syscall_snapshot();
    auto const compound_input = to_byte_string_view(val_id.bytes);

    for (uint32_t i = 0; i < 1; ++i) {
        EXPECT_EQ(
            contract.precompile_compound(compound_input, auth_address, {})
                .status,
            StakingContract::SUCCESS);
        auto const del = contract.vars.delegator(val_id, auth_address);
        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.next_delta_stake().load().native(), REWARD);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 4);
    }

    inc_epoch();

    // Epoch 3 - validator compounds touchs state
    touch_delegator(val_id, auth_address);
    {
        auto const del = contract.vars.delegator(val_id, auth_address);
        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), REWARD);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 4);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    skip_to_next_epoch();

    // Epoch 4 - Compound rewards should take effect now.
    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);
    {
        auto const del = contract.vars.delegator(val_id, auth_address);

        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE + REWARD);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

// compound delegators before and after snapshots
TEST_F(Stake, delegate_compound)
{ // epoch 1
    auto const auth_address = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(ACTIVE_VALIDATOR_STAKE);
    auto const [input, address] =
        craft_add_validator_input(auth_address, ACTIVE_VALIDATOR_STAKE);
    u64_be const val_id{1};
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);

    byte_string_view const delegate_input{
        reinterpret_cast<unsigned char const *>(&val_id), sizeof(val_id)};
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    auto const d2 = 0xbbbbaaaabbbb_address;

    EXPECT_EQ(
        StakingContract::SUCCESS,
        contract.precompile_delegate(delegate_input, d0, value).status);
    EXPECT_EQ(
        StakingContract::SUCCESS,
        contract.precompile_delegate(delegate_input, d1, value).status);
    EXPECT_EQ(
        StakingContract::SUCCESS,
        contract.precompile_delegate(delegate_input, d2, value).status);
    EXPECT_EQ(
        4 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val_id).stake().load().native());
    skip_to_next_epoch();

    // epoch 2
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    auto const compound_input = to_byte_string_view(val_id.bytes);

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 2));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 3));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d2, {}).status,
        StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 3));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 3));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE, ((REWARD / 4) * 3));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d2, {}).status,
        StakingContract::SUCCESS);

    inc_epoch();

    // Epoch 3 - compound reward is now active
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 3), 0);

    check_delegator_c_state(
        val,
        d0,
        ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 1),
        ((REWARD / 4) * 2));

    check_delegator_c_state(
        val,
        d1,
        ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 2),
        ((REWARD / 4) * 1));

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 3), 0);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    inc_epoch();
    touch_delegator(val_id, auth_address);
    touch_delegator(val_id, d0);
    touch_delegator(val_id, d1);
    touch_delegator(val_id, d2);

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 6), 0);

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 6), 0);

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 5), 0);

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 6), 0);

    skip_to_next_epoch();

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE + ((REWARD / 4) * 6), 0);
}

// compound delegators before and after snapshots then withdraw, val remains
// active
TEST_F(Stake, compound_undelegate)
{
    auto const auth_address = 0xdeadbeef_address;
    // auto const value =
    // intx::be::store<evmc_uint256be>(ACTIVE_VALIDATOR_STAKE);
    auto const [input, address] =
        craft_add_validator_input(auth_address, ACTIVE_VALIDATOR_STAKE);
    u64_be const val_id{1};
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);

    byte_string_view const delegate_input{
        reinterpret_cast<unsigned char const *>(&val_id), sizeof(val_id)};
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;

    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val_id).stake().load().native());
    skip_to_next_epoch();

    // epoch 2

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    auto const compound_input = to_byte_string_view(val_id.bytes);
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 2));

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 2));

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 2));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    uint8_t const withdrawal_id{1};

    EXPECT_EQ(
        undelegate(val.id, d0, withdrawal_id, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    check_delegator_c_state(val, d0, 0, 0);

    syscall_snapshot();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 1));

    check_delegator_c_state(val, d0, 0, 0);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val.id, d1, withdrawal_id, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    check_delegator_c_state(val, d1, 0, 0);

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    inc_epoch();
    // Epoch 3
    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + ((REWARD / 3) * 2),
        (REWARD / 3));

    check_delegator_c_state(val, d0, ((REWARD / 3) * 2), 0);

    check_delegator_c_state(val, d1, ((REWARD / 3) * 2), 0);

    skip_to_next_epoch();

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(withdraw(val.id, d0, withdrawal_id), StakingContract::SUCCESS);

    EXPECT_EQ(withdraw(val.id, d1, withdrawal_id), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(d0), ACTIVE_VALIDATOR_STAKE + ((REWARD / 3) * 2));
    EXPECT_EQ(get_balance(d1), ACTIVE_VALIDATOR_STAKE + ((REWARD / 3)));
}

TEST_F(Stake, compound_partial_undelegate)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const [input, address] =
        craft_add_validator_input(auth_address, ACTIVE_VALIDATOR_STAKE);
    u64_be const val_id{1};
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);

    byte_string_view const delegate_input{
        reinterpret_cast<unsigned char const *>(&val_id), sizeof(val_id)};
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;

    EXPECT_EQ(
        delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE), StakingContract::SUCCESS);

    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val_id).stake().load().native());
    skip_to_next_epoch();

    // epoch 2

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));
    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    auto const compound_input = to_byte_string_view(val_id.bytes);
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 2));

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 2));

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 2));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    uint8_t const withdrawal_id{1};

    EXPECT_EQ(
        undelegate(val.id, d0, withdrawal_id, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    check_delegator_c_state(val, d0, ACTIVE_VALIDATOR_STAKE / 2, 0);

    syscall_snapshot();

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((REWARD / 3) * 1));

    check_delegator_c_state(val, d0, ACTIVE_VALIDATOR_STAKE / 2, (REWARD / 6));

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d0, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, d1, {}).status,
        StakingContract::SUCCESS);

    EXPECT_EQ(
        undelegate(val.id, d1, withdrawal_id, ACTIVE_VALIDATOR_STAKE / 2),
        StakingContract::SUCCESS);

    check_delegator_c_state(val, d1, ACTIVE_VALIDATOR_STAKE / 2, 0);

    EXPECT_EQ(StakingContract::SUCCESS, syscall_reward(address));

    inc_epoch();
    // Epoch 3
    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + ((REWARD / 3) * 2),
        (REWARD / 3));

    check_delegator_c_state(
        val,
        d0,
        ACTIVE_VALIDATOR_STAKE / 2 + ((REWARD / 3) * 2),
        ((REWARD / 6)));

    check_delegator_c_state(
        val,
        d1,
        ACTIVE_VALIDATOR_STAKE / 2 + ((REWARD / 3) * 2),
        ((REWARD / 6)));

    skip_to_next_epoch();

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(withdraw(val.id, d0, withdrawal_id), StakingContract::SUCCESS);
    EXPECT_EQ(withdraw(val.id, d1, withdrawal_id), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(d0), ACTIVE_VALIDATOR_STAKE / 2 + ((REWARD / 3)));
    EXPECT_EQ(get_balance(d1), ACTIVE_VALIDATOR_STAKE / 2 + ((REWARD / 6)));

    check_delegator_c_state(
        val,
        d0,
        ACTIVE_VALIDATOR_STAKE / 2 + ((REWARD / 3) * 2) + ((REWARD / 6)),
        ((REWARD / 6)));

    check_delegator_c_state(
        val,
        d1,
        ACTIVE_VALIDATOR_STAKE / 2 + ((REWARD / 3) * 2) + ((REWARD / 3)),
        (REWARD / 6));
}

/////////////////////
// undelegate tests
/////////////////////

TEST_F(Stake, undelegate_revert_insufficent_funds)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const del_address = 0xaaaabbbb_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();

    uint8_t const withdrawal_id{1};
    EXPECT_EQ(
        undelegate(
            val.id, del_address, withdrawal_id, 1 + ACTIVE_VALIDATOR_STAKE),
        StakingContract::INSUFFICIENT_STAKE);

    touch_delegator(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        0);

    EXPECT_EQ(get_balance(del_address), 0);
}

TEST_F(Stake, undelegate_boundary_pool)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const del_address = 0xaaaabbbb_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();

    // undelegate this epoch
    uint8_t const withdrawal_id{1};
    EXPECT_EQ(
        undelegate(val.id, del_address, withdrawal_id, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    // reward during the block boundary
    syscall_snapshot();
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // skip delay
    inc_epoch();

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, del_address);

    // validator should get all the rewards since the secondary delegator
    // does not become active in the consensus view until after the window
    // expires.
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 2);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).stake().load().native(),
        0);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        0);

    EXPECT_EQ(
        withdraw(val.id, del_address, withdrawal_id),
        StakingContract::WITHDRAWAL_NOT_READY);

    // reward the validator in this epoch which the delegator should not
    // get. he has a 1 epoch delay where he continues to deactivate, and
    // another epoch delay for the slashing window in which no rewards are
    // earned.
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    skip_to_next_epoch();

    // withdrawal should succeed
    EXPECT_EQ(
        withdraw(val.id, del_address, withdrawal_id), StakingContract::SUCCESS);

    // primary delegator get all the rewards after the secondary delegator
    // becomes inactive.
    touch_delegator(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD + REWARD / 2);

    // delegator gets his principal and rewards accured during deactivation
    // period.
    EXPECT_EQ(get_balance(del_address), ACTIVE_VALIDATOR_STAKE + REWARD / 2);
}

TEST_F(Stake, undelegate_snapshot_boundary_pool)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const del_address = 0xaaaabbbb_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    EXPECT_EQ(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();

    // undelegate this epoch
    uint8_t const withdrawal_id{1};

    // reward during the block boundary
    syscall_snapshot();
    EXPECT_EQ(
        undelegate(val.id, del_address, withdrawal_id, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    // skip delay
    inc_epoch();

    touch_delegator(val.id, auth_address);
    touch_delegator(val.id, del_address);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 2);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).stake().load().native(),
        0);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        0);

    EXPECT_EQ(
        withdraw(val.id, del_address, withdrawal_id),
        StakingContract::WITHDRAWAL_NOT_READY);

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    skip_to_next_epoch();
    skip_to_next_epoch();

    // withdrawal should succeed
    EXPECT_EQ(
        withdraw(val.id, del_address, withdrawal_id), StakingContract::SUCCESS);

    touch_delegator(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD);

    EXPECT_EQ(get_balance(del_address), ACTIVE_VALIDATOR_STAKE + REWARD);
}

/////////////////////
// withdraw tests
/////////////////////

TEST_F(Stake, double_withdraw)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, MIN_VALIDATE_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();
    EXPECT_EQ(
        undelegate(val.id, auth_address, 1, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(withdraw(val.id, auth_address, 1), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        withdraw(val.id, auth_address, 1),
        StakingContract::UNKNOWN_WITHDRAWAL_ID);
    EXPECT_EQ(get_balance(auth_address), MIN_VALIDATE_STAKE);
}

TEST_F(Stake, withdraw_reusable_id)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, MIN_VALIDATE_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();
    EXPECT_EQ(
        undelegate(val.id, auth_address, 1, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);
    skip_to_next_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(withdraw(val.id, auth_address, 1), StakingContract::SUCCESS);

    EXPECT_EQ(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        undelegate(val.id, auth_address, 1, MIN_VALIDATE_STAKE),
        StakingContract::SUCCESS);

    skip_to_next_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(withdraw(val.id, auth_address, 1), StakingContract::SUCCESS);
}

/////////////////////
// claim_rewards tests
/////////////////////

TEST_F(Stake, claim_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(claim_rewards(val.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), REWARD);
}

TEST_F(Stake, claim_noop)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(claim_rewards(val.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), 0);
}

TEST_F(Stake, claim_rewards_compound)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val.status, StakingContract::SUCCESS);
    skip_to_next_epoch();
    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(claim_rewards(val.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), REWARD);

    auto const compound_input = to_byte_string_view(val.id.bytes);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    syscall_snapshot();

    EXPECT_EQ(syscall_reward(val.sign_address), StakingContract::SUCCESS);

    EXPECT_EQ(get_balance(auth_address), REWARD);
    EXPECT_EQ(claim_rewards(val.id, auth_address), StakingContract::SUCCESS);
    EXPECT_EQ(get_balance(auth_address), 2 * REWARD);

    EXPECT_EQ(
        contract.precompile_compound(compound_input, auth_address, {}).status,
        StakingContract::SUCCESS);

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, 0);
    inc_epoch();
    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, 0);
}

////////////////////////
// sys_call_reward tests
////////////////////////

TEST_F(Stake, reward_unknown_validator)
{
    auto const unknown = Address{0xabcdef};
    EXPECT_EQ(
        StakingContract::BLOCK_AUTHOR_NOT_IN_SET, syscall_reward(unknown));
}

TEST_F(Stake, reward_crash_no_snapshot_missing_validator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val1 = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);
    inc_epoch();
    EXPECT_EQ(
        StakingContract::BLOCK_AUTHOR_NOT_IN_SET,
        syscall_reward(val1.sign_address));
}

////////////////////////
// sys_call_snapshot tests
////////////////////////

////////////////////////
// sys_call_epoch_change tests
////////////////////////

TEST_F(Stake, contract_bootstrap)
{
    // This simulates the bootstrap flow. execution will deploy the
    // precompiles, but consensus won't send any snapshot or epoch change
    // txns. So everything will be added to epoch 0 and then later, a
    // snapshot will be called and the epoch will change to N. For the
    // purpose of this test, we will jump to epoch 1000.
    contract.vars.epoch.store(0);
    auto const auth_address = 0xdeadbeef_address;
    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_EQ(val1.status, StakingContract::SUCCESS);

    // Add a second validator that doesn't have enough stake to activate
    auto const val2 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1002});
    EXPECT_EQ(val2.status, StakingContract::SUCCESS);

    // add delegator
    auto const d1 = 0xaaaabbbb_address;
    EXPECT_EQ(delegate(val1.id, d1, 10 * MON), StakingContract::SUCCESS);
    // add some more
    EXPECT_EQ(
        delegate(val1.id, d1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::SUCCESS);

    // cannot undelegate before activation
    EXPECT_EQ(
        undelegate(val1.id, d1, 1, ACTIVE_VALIDATOR_STAKE),
        StakingContract::INSUFFICIENT_STAKE);

    // no withdrawals work either
    for (uint16_t i = 0; i <= std::numeric_limits<uint8_t>::max(); ++i) {
        EXPECT_EQ(
            withdraw(val1.id, d1, static_cast<uint8_t>(i)),
            StakingContract::UNKNOWN_WITHDRAWAL_ID);
    }

    syscall_snapshot();
    syscall_on_epoch_change(1000);

    // both only have their principal and no rewards
    check_delegator_c_state(val1, auth_address, MIN_VALIDATE_STAKE, 0);
    check_delegator_c_state(val1, d1, 10 * MON + ACTIVE_VALIDATOR_STAKE, 0);

    EXPECT_EQ(contract.vars._valset_consensus().length(), 1);
    EXPECT_EQ(contract.vars._valset_snapshot().length(), 0);
    EXPECT_EQ(
        contract.vars._valset_consensus().get(0).load().native(),
        val1.id.native());

    // accumulator at 0 should be cleared since all delegators have been
    // pulled up-to-date.
    auto const acc = contract.vars.acc(0, val1.id).load();
    EXPECT_EQ(acc.refcount.native(), 0);
    EXPECT_EQ(acc.value.native(), 0);

    // the inactive validator is not active but still has his principal
    check_delegator_c_state(val2, auth_address, MIN_VALIDATE_STAKE, 0);
    auto const acc2 = contract.vars.acc(0, val2.id).load();
    EXPECT_EQ(acc2.refcount.native(), 0);
    EXPECT_EQ(acc2.value.native(), 0);
}
