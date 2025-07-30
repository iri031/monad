#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <cstring>
#include <memory>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

byte_string_view consume_bytes(byte_string_view &data, size_t const num_bytes)
{
    byte_string_view ret = data.substr(0, num_bytes);
    data.remove_prefix(num_bytes);
    return ret;
}

uint256_t calculate_rewards(
    uint256_t const &stake, uint256_t const &current_acc,
    uint256_t const &last_checked_acc)
{
    auto const delta = intx::subc(current_acc, last_checked_acc);
    if (MONAD_UNLIKELY(delta.carry)) {
        return 0;
    }
    return (delta.value * stake) / UNIT_BIAS;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

StakingContract::StakingContract(State &state, Address const &ca)
    : state_{state}
    , ca_{ca}
    , vars{state, ca}
{
}

/////////////
// Events //
/////////////
void StakingContract::emit_validator_created_event(
    u64_be const val_id, Address const &auth_delegator)

{
    constexpr bytes32_t signature{
        0xab6f199d07fd15c571140b120b4b414ab3baa8b5a543b4d4f78c8319d6634974_bytes32};
    EventBuilder builder(STAKING_CONTRACT_ADDRESS, signature);
    auto const event = builder.add_topic(abi_encode_int(val_id))
                           .add_topic(abi_encode_address(auth_delegator))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_validator_status_changed_event(
    u64_be const val_id, u64_be const flags)
{
    constexpr bytes32_t signature{
        0xc95966754e882e03faffaf164883d98986dda088d09471a35f9e55363daf0c53_bytes32};
    EventBuilder builder(STAKING_CONTRACT_ADDRESS, signature);
    auto const event = builder.add_topic(abi_encode_int(val_id))
                           .add_data(abi_encode_int(flags))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_delegation_event(
    u64_be const val_id, Address const &delegator, u256_be const &amount,
    u64_be const active_epoch)

{
    constexpr bytes32_t signature{
        0xe4d4df1e1827dd28252fd5c3cd7ebccd3da6e0aa31f74c828f3c8542af49d840_bytes32};
    EventBuilder builder(STAKING_CONTRACT_ADDRESS, signature);
    auto const event = builder.add_topic(abi_encode_int(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_int(amount))
                           .add_data(abi_encode_int(active_epoch))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_undelegate_event(
    u64_be val_id, Address const &delegator, uint8_t withdrawal_id,
    u256_be amount, u64_be activation_epoch)
{
    constexpr bytes32_t signature{
        0x3e53c8b91747e1b72a44894db10f2a45fa632b161fdcdd3a17bd6be5482bac62_bytes32};
    EventBuilder builder(STAKING_CONTRACT_ADDRESS, signature);
    auto const event = builder.add_topic(abi_encode_int(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_int(withdrawal_id))
                           .add_data(abi_encode_int(amount))
                           .add_data(abi_encode_int(activation_epoch))
                           .build();
    state_.store_log(event);
}

void StakingContract::emit_claim_rewards_event(
    u64_be val_id, Address const &delegator, u256_be const &amount)
{
    constexpr bytes32_t signature{
        0x3170ba953fe3e068954fcbc93913a05bf457825d4d4d86ec9b72ce2186cd8109_bytes32};
    EventBuilder builder(STAKING_CONTRACT_ADDRESS, signature);
    auto const event = builder.add_topic(abi_encode_int(val_id))
                           .add_topic(abi_encode_address(delegator))
                           .add_data(abi_encode_int(amount))
                           .build();
    state_.store_log(event);
}

//////////////
// Helpers //
//////////////

void StakingContract::mint_tokens(uint256_t const &amount)
{
    state_.add_to_balance(ca_, amount);
}

void StakingContract::send_tokens(Address const &to, uint256_t const &amount)
{
    state_.add_to_balance(to, amount);
    state_.subtract_from_balance(ca_, amount);
}

uint64_t StakingContract::get_activation_epoch() const noexcept
{
    auto const epoch = vars.epoch.load().native();
    return vars.in_boundary.load_checked().has_value() ? epoch + 2 : epoch + 1;
}

bool StakingContract::is_epoch_active(
    uint64_t const active_epoch) const noexcept
{
    auto const current_epoch = vars.epoch.load().native();
    return active_epoch != 0 && active_epoch <= current_epoch;
}

void StakingContract::inc_acc_refcount(u64_be const epoch, u64_be const val_id)
{
    auto acc_storage = vars.acc(epoch, val_id);
    auto acc = acc_storage.load();
    acc.refcount = acc.refcount.native() + 1;
    acc_storage.store(acc);
}

u256_be
StakingContract::dec_acc_refcount(u64_be const epoch, u64_be const val_id)
{
    auto acc_storage = vars.acc(epoch, val_id);
    auto acc = acc_storage.load();
    auto const value = acc.value;
    auto const refcount = acc.refcount.native();
    if (MONAD_UNLIKELY(refcount == 0)) {
        LOG_INFO(
            "StakingContract: refcount for epoch {} and val_id {} is 0",
            epoch.native(),
            val_id.native());
        return {};
    }
    auto const new_refcount = refcount - 1;
    if (new_refcount == 0) {
        acc_storage.clear();
    }
    else {
        acc.refcount = new_refcount;
        acc_storage.store(acc);
    }
    return value;
}

bool can_promote_delta(DelInfo const &del, u64_be const &epoch)
{
    return del.get_delta_epoch().native() == 0 &&
           del.get_next_delta_epoch().native() <= epoch.native() + 1;
}

void promote_delta(DelInfo &del)
{
    del.delta_stake().store(del.next_delta_stake().load());
    del.next_delta_stake().clear();

    del.set_delta_epoch(del.get_next_delta_epoch());
    del.set_next_delta_epoch(0);
}

uint256_t StakingContract::apply_compound(u64_be const val_id, DelInfo &del)
{
    auto const epoch_acc = dec_acc_refcount(del.get_delta_epoch(), val_id);
    auto const stake = del.stake().load().native();
    auto const delta_stake = del.delta_stake().load().native();
    auto const acc = del.acc().load().native();

    auto const rewards = calculate_rewards(stake, epoch_acc.native(), acc);
    del.acc().store(epoch_acc);

    u256_be const compounded_stake = stake + delta_stake;
    del.stake().store(compounded_stake);

    // u256_be const new_rewards = del.rewards().load().native() + rewards;
    // del.rewards().store(new_rewards);
    promote_delta(del);
    return rewards;
}

Result<byte_string> reward_state_check(ValExecution &val, uint256_t rewards)
{
    bool can_claim_reward = val.unclaimed_rewards().load().native() >= rewards;

    // revert tx if claiming greater than unclaimed reward balance.
    if (MONAD_UNLIKELY(!can_claim_reward)) {
        return StakeError::InvalidInput;
    }
    u256_be const unclaimed_rewards =
        val.unclaimed_rewards().load().native() - rewards;
    val.unclaimed_rewards().store(unclaimed_rewards);

    return outcome::success();
}

Result<void> StakingContract::touch_delegator(u64_be const val_id, DelInfo &del)
{
    // move up next_delta_epoch
    if (can_promote_delta(del, vars.epoch.load())) {
        promote_delta(del);
    }
    auto val = vars.val_execution(val_id);

    bool const can_compound = is_epoch_active(del.get_delta_epoch().native());
    bool const can_compound_boundary =
        is_epoch_active(del.get_next_delta_epoch().native());
    if (MONAD_UNLIKELY(can_compound_boundary)) {
        MONAD_ASSERT(can_compound); // only set when user compounds before
                                    // and after block boundary
        auto rewards = apply_compound(val_id, del);
        BOOST_OUTCOME_TRY(reward_state_check(val, rewards));
        u256_be const new_rewards = del.rewards().load().native() + rewards;
        del.rewards().store(new_rewards);
    }
    if (MONAD_UNLIKELY(can_compound)) {
        auto rewards = apply_compound(val_id, del);
        BOOST_OUTCOME_TRY(reward_state_check(val, rewards));
        u256_be const new_rewards = del.rewards().load().native() + rewards;
        del.rewards().store(new_rewards);
    }
    auto const rewards = calculate_rewards(
        del.stake().load().native(),
        val.acc().load().native(),
        del.acc().load().native());
    BOOST_OUTCOME_TRY(reward_state_check(val, rewards));

    // update delegator state
    u256_be const new_rewards = del.rewards().load().native() + rewards;
    del.rewards().store(new_rewards);
    del.acc().store(val.acc().load());
    return outcome::success();
}

///////////////////
//  Precompiles  //
///////////////////

std::pair<StakingContract::PrecompileFunc, uint64_t>
StakingContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return make_pair(&StakingContract::precompile_fallback, 0);
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    using StakingPrecompile = std::pair<PrecompileFunc, uint64_t>;
    constexpr std::array<StakingPrecompile, 12> dispatch_table{
        make_pair(&StakingContract::precompile_fallback, 0),
        make_pair(&StakingContract::syscall_on_epoch_change, 0),
        make_pair(&StakingContract::syscall_snapshot, 0),
        make_pair(&StakingContract::syscall_reward, 0),
        make_pair(&StakingContract::precompile_get_validator, 0 /* fixme */),
        make_pair(&StakingContract::precompile_get_delegator, 0 /* fixme */),
        make_pair(&StakingContract::precompile_add_validator, 0 /* fixme */),
        make_pair(&StakingContract::precompile_delegate, 0 /* fixme */),
        make_pair(&StakingContract::precompile_undelegate, 0 /* fixme */),
        make_pair(&StakingContract::precompile_compound, 0 /* fixme */),
        make_pair(&StakingContract::precompile_withdraw, 0 /* fixme */),
        make_pair(&StakingContract::precompile_claim_rewards, 0 /* fixme */)};

    if (MONAD_UNLIKELY(signature >= dispatch_table.size())) {
        return make_pair(&StakingContract::precompile_fallback, 0);
    }

    return dispatch_table[signature];
}

Result<byte_string> StakingContract::precompile_get_validator(
    byte_string_view const input, evmc_address const &, evmc_uint256be const &)
{
    if (MONAD_UNLIKELY(input.size() != sizeof(u64_be) /* validator id */)) {
        return StakeError::InvalidInput;
    }
    auto const val_id = unaligned_load<u64_be>(input.data());
    auto const val = vars.val_execution(val_id);
    return val.abi_encode();
}

Result<byte_string> StakingContract::precompile_get_delegator(
    byte_string_view const input, evmc_address const &, evmc_uint256be const &)
{
    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */ +
                                    sizeof(Address) /* delegator address */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakeError::InvalidInput;
    }
    auto const val_id = unaligned_load<u64_be>(input.data());
    auto const address = unaligned_load<Address>(input.data() + sizeof(u64_be));
    auto del = vars.delegator(val_id, address);
    touch_delegator(val_id, del).value();
    return del.abi_encode();
}

Result<byte_string> StakingContract::precompile_fallback(
    byte_string_view const, evmc_address const &, evmc_uint256be const &)
{
    return StakeError::MethodNotSupported;
}

// TODO: Track solvency
Result<byte_string> StakingContract::precompile_add_validator(
    byte_string_view const input, evmc_address const &,
    evmc_uint256be const &msg_value)
{
    constexpr size_t MESSAGE_SIZE = 33 /* compressed secp pubkey */ +
                                    48 /* compressed bls pubkey */ +
                                    sizeof(Address) /* auth address */ +
                                    sizeof(u256_be) /* signed stake */ +
                                    sizeof(u256_be) /* commission rate */;
    constexpr size_t SIGNATURES_SIZE =
        64 /* secp signature */ + 96 /* bls signature */;

    constexpr size_t EXPECTED_INPUT_SIZE = MESSAGE_SIZE + SIGNATURES_SIZE;

    // Validate input size
    if (MONAD_UNLIKELY(input.size() != EXPECTED_INPUT_SIZE)) {
        return StakeError::InvalidInput;
    }

    // extract individual inputs
    byte_string_view message = input.substr(0, MESSAGE_SIZE);

    byte_string_view reader = input;
    auto const secp_pubkey_serialized =
        unaligned_load<byte_string_fixed<33>>(consume_bytes(reader, 33).data());
    auto const bls_pubkey_serialized =
        unaligned_load<byte_string_fixed<48>>(consume_bytes(reader, 48).data());
    auto const auth_address =
        unaligned_load<Address>(consume_bytes(reader, sizeof(Address)).data());
    auto const signed_stake = unaligned_load<evmc_uint256be>(
        consume_bytes(reader, sizeof(evmc_uint256be)).data());
    auto const commission =
        unaligned_load<u256_be>(consume_bytes(reader, sizeof(u256_be)).data());
    auto const secp_signature_serialized =
        unaligned_load<byte_string_fixed<64>>(consume_bytes(reader, 64).data());
    auto const bls_signature_serialized =
        unaligned_load<byte_string_fixed<96>>(consume_bytes(reader, 96).data());
    if (!reader.empty()) {
        return StakeError::InvalidInput;
    }

    if (MONAD_UNLIKELY(
            0 !=
            memcmp(
                signed_stake.bytes, msg_value.bytes, sizeof(evmc_uint256be)))) {
        return StakeError::InvalidInput;
    }

    auto const stake = intx::be::load<uint256_t>(msg_value);
    if (MONAD_UNLIKELY(stake < MIN_VALIDATE_STAKE)) {
        return StakeError::InsufficientStake;
    }

    // Verify SECP signature
    Secp256k1_Pubkey secp_pubkey(secp_pubkey_serialized);
    if (MONAD_UNLIKELY(!secp_pubkey.is_valid())) {
        return StakeError::InvalidSecpPubkey;
    }
    Secp256k1_Signature secp_sig(secp_signature_serialized);
    if (MONAD_UNLIKELY(!secp_sig.is_valid())) {
        return StakeError::InvalidSecpSignature;
    }
    if (MONAD_UNLIKELY(!secp_sig.verify(secp_pubkey, message))) {
        return StakeError::SecpSignatureVerificationFailed;
    }

    // Verify BLS signature
    Bls_Pubkey bls_pubkey(bls_pubkey_serialized);
    if (MONAD_UNLIKELY(!bls_pubkey.is_valid())) {
        return StakeError::InvalidBlsPubkey;
    }
    Bls_Signature bls_sig(bls_signature_serialized);
    if (MONAD_UNLIKELY(!bls_sig.is_valid())) {
        return StakeError::InvalidBlsSignature;
    }
    if (MONAD_UNLIKELY(!bls_sig.verify(bls_pubkey, message))) {
        return StakeError::BlsSignatureVerificationFailed;
    }

    // check commission rate doesn't exceed 100%
    // note that: delegator_reward = (raw_reward * 1e18) / 1e18
    if (MONAD_UNLIKELY(commission.native() > MON)) {
        return StakeError::InvalidInput;
    }

    // Check if validator already exists
    auto const secp_eth_address = address_from_secpkey(secp_pubkey.serialize());
    auto const bls_eth_address = address_from_bls_key(bls_pubkey.serialize());
    auto val_id_storage = vars.val_id(secp_eth_address);
    auto val_id_bls_storage = vars.val_id_bls(bls_eth_address);
    if (MONAD_UNLIKELY(
            val_id_storage.load_checked().has_value() ||
            val_id_bls_storage.load_checked().has_value())) {
        return StakeError::ValidatorExists;
    }

    u64_be const val_id = vars.last_val_id.load().native() + 1;
    val_id_storage.store(val_id);
    val_id_bls_storage.store(val_id);
    vars.last_val_id.store(val_id);

    // add validator metadata
    auto val = vars.val_execution(val_id);
    val.keys().store(
        KeysPacked{
            .secp_pubkey = secp_pubkey_serialized,
            .bls_pubkey = bls_pubkey_serialized});
    val.address_flags().store(
        AddressFlags{
            .auth_address = auth_address, .flags = ValidatorFlagsStakeTooLow});
    val.commission().store(commission);

    // add to valset
    vars.valset_execution.push(val_id);

    emit_validator_created_event(val_id, auth_address);

    BOOST_OUTCOME_TRY(delegate(val_id, stake, auth_address));
    return byte_string{abi_encode_int(val_id)};
}

Result<void> StakingContract::delegate(
    u64_be const val_id, uint256_t const &stake, Address const &address)
{
    auto val = vars.val_execution(val_id);
    if (MONAD_UNLIKELY(!val.exists())) {
        return StakeError::UnknownValidator;
    }

    auto del = vars.delegator(val_id, address);
    touch_delegator(val_id, del).value();

    bool need_future_accumulator = false;
    u64_be const active_epoch = get_activation_epoch();

    // re-delegation: check if stake needs to be compounded, and when.
    if (vars.in_boundary.load()) {
        // case 1: compound called in boundary. becomes active in epoch+2
        need_future_accumulator = (del.get_next_delta_epoch().native() == 0);
        uint256_t const compound_stake = del.next_delta_stake().load().native();
        del.next_delta_stake().store(compound_stake + stake);
        del.set_next_delta_epoch(active_epoch);
    }
    else {
        // case 2: compound called before boundary. becomes active in
        // epoch+1
        need_future_accumulator = (del.get_delta_epoch().native() == 0);
        uint256_t const compound_stake = del.delta_stake().load().native();
        del.delta_stake().store(compound_stake + stake);
        del.set_delta_epoch(active_epoch);
    }

    if (need_future_accumulator) {
        inc_acc_refcount(active_epoch, val_id);
    }
    emit_delegation_event(val_id, address, stake, active_epoch);

    auto const new_val_stake = val.stake().load().native() + stake;
    val.stake().store(new_val_stake);

    // does total val stake exceed the minimum threshold?
    if (new_val_stake >= ACTIVE_VALIDATOR_STAKE &&
        (val.get_flags() & ValidatorFlagsStakeTooLow)) {
        val.clear_flag(ValidatorFlagsStakeTooLow);
    }

    // did the auth delegator reactivate?
    if (val.auth_address() == address &&
        (val.get_flags() & ValidatorFlagWithdrawn) &&
        del.get_next_epoch_stake() >= MIN_VALIDATE_STAKE) {
        val.clear_flag(ValidatorFlagWithdrawn);
    }

    return outcome::success();
}

Result<byte_string> StakingContract::precompile_delegate(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    // Validate input size
    if (MONAD_UNLIKELY(input.size() != sizeof(u64_be) /* validator id */)) {
        return StakeError::InvalidInput;
    }

    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());
    auto const stake = intx::be::load<uint256_t>(msg_value);

    if (MONAD_UNLIKELY(stake == 0)) {
        return StakeError::InsufficientStake;
    }
    BOOST_OUTCOME_TRY(delegate(val_id, stake, msg_sender));
    return byte_string{};
}

Result<byte_string> StakingContract::precompile_undelegate(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &)
{
    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */ +
                                    sizeof(u256_be) /* amount */ +
                                    sizeof(uint8_t) /* withdrawal id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakeError::InvalidInput;
    }

    byte_string_view reader = input;
    auto const val_id =
        unaligned_load<u64_be>(consume_bytes(reader, sizeof(u64_be)).data());
    uint256_t const amount =
        unaligned_load<u256_be>(consume_bytes(reader, sizeof(u256_be)).data())
            .native();
    auto const withdrawal_id =
        unaligned_load<uint8_t>(consume_bytes(reader, sizeof(uint8_t)).data());

    if (MONAD_UNLIKELY(amount == 0)) {
        return byte_string{};
    }

    auto val = vars.val_execution(val_id);
    if (MONAD_UNLIKELY(!val.exists())) {
        return StakeError::UnknownValidator;
    }

    auto withdrawal_request =
        vars.withdrawal_request(val_id, msg_sender, withdrawal_id)
            .load_checked();
    if (MONAD_UNLIKELY(withdrawal_request.has_value())) {
        return StakeError::WithdrawalIdExists;
    }

    auto del = vars.delegator(val_id, msg_sender);
    touch_delegator(val_id, del).value();
    uint256_t val_stake = val.stake().load().native();
    uint256_t del_stake = del.stake().load().native();

    if (MONAD_UNLIKELY(del_stake < amount)) {
        return StakeError::InsufficientStake;
    }

    if (MONAD_UNLIKELY(val_stake < amount)) {
        LOG_ERROR(
            "Staking: Insolvency risk: id={}, stake={} undelegate_amt={}",
            val_id.native(),
            val_stake,
            amount);
        return StakeError::InternalError;
    }

    val_stake -= amount;
    del_stake -= amount;
    val.stake().store(val_stake);
    del.stake().store(del_stake);

    if (msg_sender == val.auth_address() &&
        del.get_next_epoch_stake() < MIN_VALIDATE_STAKE) {
        emit_validator_status_changed_event(val_id, val.get_flags());
        val.set_flag(ValidatorFlagWithdrawn);
    }
    if (val_stake < ACTIVE_VALIDATOR_STAKE) {
        emit_validator_status_changed_event(val_id, val.get_flags());
        val.set_flag(ValidatorFlagsStakeTooLow);
    }

    u64_be const withdrawal_epoch = get_activation_epoch();

    emit_undelegate_event(
        val_id, msg_sender, withdrawal_id, amount, withdrawal_epoch);

    // each withdrawal request can be thought of as an independent delegator
    // whose stake is the amount being withdrawn.
    vars.withdrawal_request(val_id, msg_sender, withdrawal_id)
        .store(
            WithdrawalRequest{
                .amount = amount,
                .acc = del.acc().load(),
                .epoch = withdrawal_epoch});
    inc_acc_refcount(withdrawal_epoch, val_id);

    return byte_string{};
}

// TODO: No compounds allowed if auth_address is under sufficent amount.
Result<byte_string> StakingContract::precompile_compound(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &)
{
    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validatorId */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakeError::InvalidInput;
    }

    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());

    auto del = vars.delegator(val_id, msg_sender);
    touch_delegator(val_id, del).value();
    auto const rewards = del.rewards().clear().native();

    if (MONAD_UNLIKELY(rewards != 0)) {
        BOOST_OUTCOME_TRY(delegate(val_id, rewards, msg_sender));
    }

    return byte_string{};
}

Result<byte_string> StakingContract::precompile_withdraw(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &)
{
    constexpr size_t MESSAGE_SIZE =
        sizeof(u64_be) /* validator id */ + sizeof(uint8_t) /* withdrawal id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakeError::InvalidInput;
    }
    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());
    auto const withdrawal_id = unaligned_load<uint8_t>(
        input.substr(sizeof(u64_be), sizeof(uint8_t)).data());

    auto withdrawal_request_storage =
        vars.withdrawal_request(val_id, msg_sender, withdrawal_id);
    auto withdrawal_request = withdrawal_request_storage.load_checked();
    if (MONAD_UNLIKELY(!withdrawal_request.has_value())) {
        return StakeError::UnknownWithdrawalId;
    }
    withdrawal_request_storage.clear();

    bool const ready =
        is_epoch_active(withdrawal_request->epoch.native() + WITHDRAWAL_DELAY);
    if (MONAD_UNLIKELY(!ready)) {
        return StakeError::WithdrawalNotReady;
    }

    auto withdraw_acc =
        dec_acc_refcount(withdrawal_request->epoch, val_id).native();
    auto amount = withdrawal_request->amount.native();
    auto const rewards = calculate_rewards(
        amount, withdraw_acc, withdrawal_request->acc.native());
    auto val = vars.val_execution(val_id);
    reward_state_check(val, rewards);

    amount += rewards;

    auto const contract_balance =
        intx::be::load<uint256_t>(state_.get_balance(ca_));
    MONAD_ASSERT(contract_balance >= amount);
    send_tokens(msg_sender, amount);

    return byte_string{};
}

Result<byte_string> StakingContract::precompile_claim_rewards(
    byte_string_view const input, evmc_address const &msg_sender,
    evmc_uint256be const &)
{
    constexpr size_t MESSAGE_SIZE = sizeof(u64_be) /* validator id */;
    if (MONAD_UNLIKELY(input.size() != MESSAGE_SIZE)) {
        return StakeError::InvalidInput;
    }
    auto const val_id =
        unaligned_load<u64_be>(input.substr(0, sizeof(u64_be)).data());

    auto del = vars.delegator(val_id, msg_sender);
    touch_delegator(val_id, del).value();

    auto const rewards = del.rewards().load();
    if (MONAD_LIKELY(rewards.native() != 0)) {
        send_tokens(msg_sender, rewards.native());
        del.rewards().clear();
        emit_claim_rewards_event(val_id, msg_sender, rewards);
    }

    return byte_string{};
}

////////////////////
//  System Calls  //
////////////////////

Result<byte_string> StakingContract::syscall_on_epoch_change(
    byte_string_view const input, evmc_address const &, evmc_uint256be const &)
{
    if (MONAD_UNLIKELY(input.size() != sizeof(u64_be))) {
        return StakeError::InvalidInput;
    }

    auto const next_epoch = unaligned_load<u64_be>(input.data());
    auto const last_epoch = vars.epoch.load();
    if (MONAD_UNLIKELY(next_epoch == last_epoch)) {
        return byte_string{};
    }

    vars.epoch.store(next_epoch);
    vars.in_boundary.clear();

    uint64_t const num_validators = vars.valset_execution.length();
    for (uint64_t i = 0; i < num_validators; i += 1) {
        auto const val_id = vars.valset_execution.get(i).load();
        auto val = vars.val_execution(val_id);

        // TODO: once Maged's speculative execution is merged, move this
        // into a separate loop.
        auto acc_storage = vars.acc(next_epoch, val_id);
        auto acc = acc_storage.load_checked();
        if (acc.has_value()) {
            acc->value = val.acc().load();
            acc_storage.store(*acc);
        }
    }

    return byte_string{};
}

// update rewards for leader only if in active validator set
Result<byte_string> StakingContract::syscall_reward(
    byte_string_view const input, evmc_address const &, evmc_uint256be const &)
{
    if (MONAD_UNLIKELY(input.size() != sizeof(Address))) {
        return StakeError::InvalidInput;
    }
    auto const block_author = unaligned_load<Address>(input.data());

    // 1. get validator information
    auto const val_id = vars.val_id(block_author).load_checked();
    if (MONAD_UNLIKELY(!val_id.has_value())) {
        return StakeError::BlockAuthorNotInSet;
    }

    // 2. validator must be active
    auto const val_consensus = vars.val_consensus(val_id.value());
    uint256_t const active_stake = val_consensus.stake().load().native();
    if (MONAD_UNLIKELY(active_stake == 0)) {
        // Validator cannot be in the active set with no stake
        return StakeError::BlockAuthorNotInSet;
    }

    mint_tokens(REWARD);

    // 3. subtract commission
    auto val_execution = vars.val_execution(val_id.value());
    uint256_t const commission = val_execution.commission().load().native();
    uint256_t const commission_reward = (REWARD * commission) / MON;

    auto auth = vars.delegator(val_id.value(), val_execution.auth_address());
    u256_be const new_rewards =
        auth.rewards().load().native() + commission_reward;
    auth.rewards().store(new_rewards);

    // 4. reward wrt to accumulator
    uint256_t const delegator_reward = REWARD - commission_reward;
    uint256_t acc = ((delegator_reward * UNIT_BIAS) / active_stake);
    val_execution.acc().store(val_execution.acc().load().native() + acc);

    // 5. update unclaimed rewards
    u256_be const unclaimed_rewards =
        val_execution.unclaimed_rewards().load().native() + delegator_reward;
    val_execution.unclaimed_rewards().store(unclaimed_rewards);
    return byte_string{};
}

Result<byte_string> StakingContract::syscall_snapshot(
    byte_string_view const input, evmc_address const &, evmc_uint256be const &)
{
    if (MONAD_UNLIKELY(!input.empty())) {
        return StakeError::InvalidInput;
    }
    if (MONAD_UNLIKELY(vars.in_boundary.load())) {
        auto const epoch = vars.epoch.load();
        LOG_WARNING("Called snapshot twice in epoch: {}", epoch.native());
        return byte_string{};
    }

    // swap the current consensus view for this epoch to the snapshot
    vars.consensus_valset_pointer.store(vars.deref_snapshot_valset());
    vars.consensus_valinfo_pointer.store(vars.deref_snapshot_valinfo());

    // seal consensus view for the next epoch with the current execution
    // state.
    //
    // while this method may appear expensive, the validator set is already
    // loaded in memory. futhermore, the only writes will be the deltas on
    // the stake slot.

    auto valset_consensus = vars.valset_consensus();
    while (!valset_consensus.empty()) {
        u64_be const val_id = valset_consensus.pop();
        auto val = vars.val_consensus(val_id);
        val.stake().clear();
        val.keys().clear();
    }
    uint64_t const num_validators = vars.valset_execution.length();
    for (uint64_t i = 0; i < num_validators; i += 1) {
        auto const val_id = vars.valset_execution.get(i).load();
        auto const val_execution = vars.val_execution(val_id);
        // TODO: once Maged's speculative execution is merged, move this
        // into a separate loop.
        auto const flags = val_execution.get_flags();
        if (MONAD_LIKELY(flags == ValidatorFlagsOk)) {
            valset_consensus.push(val_id);
            auto val_consensus = vars.val_consensus(val_id);
            val_consensus.stake().store(val_execution.stake().load());
            val_consensus.keys().store(val_execution.keys().load());
        }
    }

    vars.in_boundary.store(true);

    return byte_string{};
}

MONAD_NAMESPACE_END
