#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/monad/staking/fuzzer/staking_contract_model.hpp>

namespace
{
    using namespace monad;

    Result<u64_be> decode_u64_be_result(Result<byte_string> &&res)
    {
        BOOST_OUTCOME_TRY(auto const output, std::move(res));
        MONAD_ASSERT(output.size() == 32);
        u64_be x;
        std::memcpy(x.bytes, output.data() + 24, 8);
        return x;
    }

    Result<void> decode_true_result(Result<byte_string> &&res)
    {
        BOOST_OUTCOME_TRY(auto const output, std::move(res));
        MONAD_ASSERT(output.size() == 32);
        MONAD_ASSERT(output[31] == 1);
        return outcome::success();
    }
}

namespace monad::staking::test
{
    StakingContractModel::StakingContractModel()
    {
        trie_db_.commit(
            StateDeltas{
                {STAKING_CA,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 0, .nonce = 1}}}}},
            Code{},
            NULL_HASH_BLAKE3,
            BlockHeader{},
            {},
            {},
            {},
            {},
            {},
            {});
        trie_db_.finalize(0, NULL_HASH_BLAKE3);
        trie_db_.set_block_and_prefix(0);

        state_.add_to_balance(STAKING_CA, 0); // create account like a txn would
    }

    uint256_t StakingContractModel::delegator_stake(
        u64_be v, Address const &a, u64_be e)
    {
        return get_delegator_stake(
            v.native(),
            intx::be::load<uint256_t>(a),
            e.native());
    }

    uint256_t StakingContractModel::withdrawal_stake(
        u64_be v, Address const &a, u64_be e)
    {
        return get_withdrawal_stake(
            v.native(),
            intx::be::load<uint256_t>(a),
            e.native());
    }

    uint256_t StakingContractModel::active_consensus_commission(u64_be val_id)
    {
        return active_consensus_commission_[val_id.native()];
    }

    uint256_t StakingContractModel::active_consensus_stake(u64_be val_id)
    {
        return active_consensus_stake_[val_id.native()];
    }

    uint256_t StakingContractModel::error_bound()
    {
        return error_bound_;
    }

    bool StakingContractModel::in_epoch_delay_period()
    {
        return
            contract_.vars.in_epoch_delay_period.load_checked().has_value();
    }

    uint64_t StakingContractModel::last_val_id()
    {
        return contract_.vars.last_val_id.load().native();
    }

    uint64_t StakingContractModel::epoch()
    {
        return contract_.vars.epoch.load().native();
    }

    ValExecution StakingContractModel::val_execution(u64_be v)
    {
        return contract_.vars.val_execution(v);
    }

    StorageVariable<StakingContract::WithdrawalRequest>
    StakingContractModel::withdrawal_request(
        u64_be val_id, Address const &delegator, u8_be wid)
    {
        return contract_.vars.withdrawal_request(val_id, delegator, wid);
    }

    Delegator StakingContractModel::delegator(u64_be v, Address const &a)
    {
        return contract_.vars.delegator(v, a);
    }

    StorageArray<u64_be> StakingContractModel::valset_execution()
    {
        return contract_.vars.valset_execution;
    }

    StorageArray<u64_be> StakingContractModel::valset_snapshot()
    {
        return contract_.vars.valset_snapshot;
    }

    StorageArray<u64_be> StakingContractModel::valset_consensus()
    {
        return contract_.vars.valset_consensus;
    }

    ConsensusView StakingContractModel::consensus_view(u64_be v)
    {
        return contract_.vars.consensus_view(v);
    }

    ConsensusView StakingContractModel::snapshot_view(u64_be v)
    {
        return contract_.vars.snapshot_view(v);
    }

    StorageVariable<u256_be>
    StakingContractModel::val_bitset_bucket(u64_be v)
    {
        return contract_.vars.val_bitset_bucket(v);
    }

    std::vector<Address>
    StakingContractModel::get_delegators_for_validator(u64_be val_id)
    {
        auto const [done, _, ds] = contract_.get_delegators_for_validator(
            val_id, Address{}, std::numeric_limits<uint32_t>::max());
        MONAD_ASSERT(done);
        return ds;
    }

    uint256_t StakingContractModel::calculate_rewards(
        uint256_t const &x, uint256_t const & q, uint256_t const &p)
    {
        return (x * (q - p)) / UNIT_BIAS;
    }

    uint256_t StakingContractModel::withdrawal_reward(
        u64_be val_id, Address const &addr, u8_be id)
    {
        auto withdraw =
            contract_.vars.withdrawal_request(val_id, addr, id).load();
        auto const x = withdraw.amount.native();
        auto const q = contract_.vars.accumulated_reward_per_token(
            withdraw.epoch, val_id).load().value.native();
        auto const p = withdraw.acc.native();
        return calculate_rewards(x, q, p);
    }

    uint256_t StakingContractModel::unaccumulated_rewards(
        u64_be v, evmc_address const &a)
    {
        auto del = contract_.vars.delegator(v, a);
        auto const epoch = contract_.vars.epoch.load().native();
        auto const delta_epoch = del.get_delta_epoch();
        auto const next_delta_epoch = del.get_next_delta_epoch();

        auto const t1 = del.stake().load().native();
        auto const q1 = del.accumulated_reward_per_token().load().native();
        auto const d1 = contract_.vars.accumulated_reward_per_token(
            delta_epoch, v).load().value.native();
        uint256_t p1 = q1;
        if (delta_epoch.native() != 0 && delta_epoch.native() <= epoch) {
            p1 = d1;
        }
        auto const r1 = calculate_rewards(t1, q1, p1);

        auto t2 = t1;
        if (delta_epoch.native() <= epoch) {
            t2 += del.delta_stake().load().native();
        }
        auto const q2 = p1;
        auto const d2 = contract_.vars.accumulated_reward_per_token(
            next_delta_epoch, v).load().value.native();
        auto p2 = q2;
        if (next_delta_epoch.native() != 0 &&
            next_delta_epoch.native() <= epoch) {
            p2 = d2;
        }
        auto const r2 = calculate_rewards(t2, q2, p2);

        auto t3 = t2;
        if (next_delta_epoch.native() <= epoch) {
            t3 += del.next_delta_stake().load().native();
        }
        auto const q3 = p2;
        auto val = contract_.vars.val_execution(v);
        auto const p3 = val.accumulated_reward_per_token().load().native();
        auto const r3 = calculate_rewards(t3, q3, p3);

        return r1 + r2 + r3;
    }

    uint256_t StakingContractModel::pending_rewards(
        u64_be v, evmc_address const &a)
    {
        uint256_t sum{};
        for (size_t i = 0; i < 256; ++i) {
            sum += withdrawal_reward(v, a, static_cast<uint8_t>(i));
        }
        return sum + unaccumulated_rewards(v, a);
    }

    Result<void>
    StakingContractModel::syscall_on_epoch_change(u64_be next_epoch)
    {
        auto const input = abi_encode_uint(next_epoch);
        pre_call(evmc_uint256be{});
        auto res = contract_.syscall_on_epoch_change(input);
        post_call(res);
        if (res.has_value()) {
            active_consensus_stake_.clear();
            active_consensus_commission_.clear();
            auto valset_consensus = contract_.vars.valset_consensus;
            uint64_t const n = valset_consensus.length();
            for (uint64_t i = 0; i < n; ++i) {
                u64_be const val_id = valset_consensus.get(i).load();
                auto consensus_view = contract_.vars.consensus_view(val_id);
                active_consensus_stake_[val_id.native()] =
                    consensus_view.stake().load().native();
                active_consensus_commission_[val_id.native()] =
                    consensus_view.commission().load().native();
            }
        }
        return res;
    }

    Result<void> StakingContractModel::syscall_snapshot()
    {
        pre_call(evmc_uint256be{});
        auto res = contract_.syscall_snapshot({});
        post_call(res);
        return res;
    }

    Result<void> StakingContractModel::syscall_reward(
        Address const &addr, u256_be const &reward)
    {
        auto const input = abi_encode_address(addr);
        pre_call(evmc_uint256be{});
        auto res = contract_.syscall_reward(input, reward.native());
        post_call(res);
        return res;
    }

    Result<u64_be> StakingContractModel::precompile_add_validator(
        byte_string_view message,
        byte_string_view secp_signature,
        byte_string_view bls_signature,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("addValidator(bytes,bytes,bytes)"));
        encoder.add_bytes(message);
        encoder.add_bytes(secp_signature);
        encoder.add_bytes(bls_signature);
        auto const input = encoder.encode_final();

        auto res = dispatch(input, sender, value);
        BOOST_OUTCOME_TRY(
            auto const val_id,
            decode_u64_be_result(std::move(res)));

        byte_string_view reader{message};
        reader.remove_prefix(81);
        auto const addr = unaligned_load<Address>(
            reader.substr(0, sizeof(Address)).data());

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
           ? contract_.vars.epoch.load().native() + 2
           : contract_.vars.epoch.load().native() + 1;

        add_delegator_stake(
            val_id.native(),
            intx::be::load<uint256_t>(addr.bytes),
            epoch,
            intx::be::load<uint256_t>(value.bytes));

        return val_id;
    }

    Result<void> StakingContractModel::precompile_delegate(
        u64_be val_id,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("delegate(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();

        auto res = dispatch(input, sender, value);
        BOOST_OUTCOME_TRY(decode_true_result(std::move(res)));

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
           ? contract_.vars.epoch.load().native() + 2
           : contract_.vars.epoch.load().native() + 1;

        add_delegator_stake(
            val_id.native(),
            intx::be::load<uint256_t>(sender.bytes),
            epoch,
            intx::be::load<uint256_t>(value.bytes));

        error_bound_ += 3;

        return outcome::success();
    }

    Result<void> StakingContractModel::precompile_undelegate(
        u64_be val_id,
        u256_be const &stake,
        u8_be withdrawal_id,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("undelegate(uint64,uint256,uint8)"));
        encoder.add_uint(val_id);
        encoder.add_uint(stake);
        encoder.add_uint(withdrawal_id);
        auto const input = encoder.encode_final();

        auto res = dispatch(input, sender, value);
        BOOST_OUTCOME_TRY(decode_true_result(std::move(res)));

        auto const this_epoch = contract_.vars.epoch.load().native();

        auto const before = get_delegator_stake(
            val_id.native(),
            intx::be::load<uint256_t>(sender),
            this_epoch);
        auto const effective_undel =
            before - stake.native() >= DUST_THRESHOLD
            ? stake.native()
            : before;

        add_delegator_stake(
            val_id.native(),
            intx::be::load<uint256_t>(sender.bytes),
            this_epoch,
            -effective_undel);

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
           ? this_epoch + 2
           : this_epoch + 1;

        add_withdrawal_stake(
            val_id.native(),
            intx::be::load<uint256_t>(sender.bytes),
            epoch,
            effective_undel);

        error_bound_ += 3;

        return outcome::success();
    }

    Result<void> StakingContractModel::precompile_compound(
        u64_be val_id,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        auto const stake =
            unaccumulated_rewards(val_id, sender) +
            contract_.vars.delegator(
                val_id, sender).rewards().load().native();

        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("compound(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();
        auto res = dispatch(input, sender, value);
        BOOST_OUTCOME_TRY(decode_true_result(std::move(res)));

        auto const epoch = contract_.vars.in_epoch_delay_period.load()
           ? contract_.vars.epoch.load().native() + 2
           : contract_.vars.epoch.load().native() + 1;

        add_delegator_stake(
            val_id.native(),
            intx::be::load<uint256_t>(sender.bytes),
            epoch,
            stake);

        error_bound_ += 3;

        return outcome::success();
    }

    Result<void> StakingContractModel::precompile_withdraw(
        u64_be val_id,
        u8_be withdrawal_id,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("withdraw(uint64,uint8)"));
        encoder.add_uint(val_id);
        encoder.add_uint(withdrawal_id);
        auto const input = encoder.encode_final();
        auto res = dispatch(input, sender, value);
        if (res.has_value()) {
            error_bound_ += 1;
        }
        return decode_true_result(std::move(res));
    }

    Result<void> StakingContractModel::precompile_claim_rewards(
        u64_be val_id,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(abi_encode_selector("claimRewards(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();
        auto res = dispatch(input, sender, value);
        if (res.has_value()) {
            error_bound_ += 3;
        }
        return decode_true_result(std::move(res));
    }

    Result<void> StakingContractModel::precompile_change_commission(
        u64_be val_id,
        u256_be const &new_commission,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("changeCommission(uint64,uint256)"));
        encoder.add_uint<u64_be>(val_id);
        encoder.add_uint<u256_be>(new_commission);
        auto const input = encoder.encode_final();
        auto res = dispatch(input, sender, value);
        return decode_true_result(std::move(res));
    }

    Result<void> StakingContractModel::precompile_external_reward(
        u64_be val_id,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("externalReward(uint64)"));
        encoder.add_uint<u64_be>(val_id);
        auto const input = encoder.encode_final();
        auto res = dispatch(input, sender, value);
        if (res.has_value()) {
            auto const rew = intx::be::load<uint256_t>(value.bytes);
            distribute_reward(val_id, u256_be{rew});
        }
        return decode_true_result(std::move(res));
    }

    Result<void> StakingContractModel::precompile_get_delegator(
        u64_be val_id,
        Address const &addr,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        AbiEncoder encoder;
        encoder.add_uint<u32_be>(
            abi_encode_selector("getDelegator(uint64,address)"));
        encoder.add_uint<u64_be>(val_id);
        encoder.add_address(addr);
        auto const input = encoder.encode_final();
        BOOST_OUTCOME_TRY(dispatch(input, sender, value));
        error_bound_ += 3;
        return outcome::success();
    }

    uint256_t StakingContractModel::get_delegator_stake(
        uint64_t val_id, uint256_t const &addr, uint64_t epoch)
    {
        auto const &m = delegator_stake_[{val_id, addr}];
        auto it = m.lower_bound(epoch);
        return it == m.end() ? uint256_t{} : it->second;
    }

    uint256_t StakingContractModel::get_withdrawal_stake(
        uint64_t val_id, uint256_t const &addr, uint64_t epoch)
    {
        return withdrawal_stake_[{val_id, addr, epoch}];
    }

    void StakingContractModel::add_delegator_stake(
        uint64_t val_id, uint256_t const &addr,
        uint64_t epoch, uint256_t const &delta)
    {
        auto &m = delegator_stake_[{val_id, addr}];
        auto const prev = get_delegator_stake(val_id, addr, epoch);
        m[epoch] = prev + delta;
        auto it = m.find(epoch);
        MONAD_VM_ASSERT(it != m.end());
        // Update stake of all elements with key > epoch:
        for (;;) {
            if (it == m.begin()) {
                break;
            }
            --it;
            it->second += delta;
        }
    }

    void StakingContractModel::add_withdrawal_stake(
        uint64_t val_id, uint256_t const &addr,
        uint64_t end_epoch, uint256_t const &delta)
    {
        uint64_t const begin_epoch = contract_.vars.epoch.load().native();
        for (uint64_t e = begin_epoch; e < end_epoch; ++e) {
            withdrawal_stake_[{val_id, addr, e}] += delta;
        }
    }

    void StakingContractModel::distribute_reward(
        u64_be val_id, u256_be const &reward_be)
    {
        auto const v = val_id.native();
        auto valex = contract_.vars.val_execution(val_id);
        auto const aa = intx::be::load<uint256_t>(valex.auth_address().bytes);
        auto const rew = reward_be.native();
        auto const c = (rew * active_consensus_commission_[v]) / MON;
        auto const rr = ((rew - c) * UNIT_BIAS) / active_consensus_stake_[v];

        auto const [done, next_, dels] =
            contract_.get_delegators_for_validator(
                val_id, Address{}, std::numeric_limits<uint32_t>::max());
        MONAD_ASSERT(done);
        auto const epoch = contract_.vars.epoch.load().native();
        for (auto const &d : dels) {
            auto const a = intx::be::load<uint256_t>(d.bytes);
            auto x =
                get_delegator_stake(v, a, epoch) +
                get_withdrawal_stake(v, a, epoch);
            x *= rr;
            if (a == aa) {
                x += c * UNIT_BIAS;
            }
            unit_bias_rewards_[{v, a}] += x;
        }
    }

    void StakingContractModel::pre_call(evmc_uint256be const &value)
    {
        state_.push();
        state_.add_to_balance(
            STAKING_CA, intx::be::load<uint256_t>(value.bytes));
    }

    template <typename T>
    void StakingContractModel::post_call(Result<T> const &res)
    {
        if (res.has_value()) {
            state_.pop_accept();
        }
        else {
            state_.pop_reject();
        }
    }

    Result<byte_string> StakingContractModel::dispatch(
        byte_string const & input,
        evmc_address const &sender,
        evmc_uint256be const &value)
    {
        pre_call(value);
        byte_string_view msg_input(input);
        msg_input.remove_prefix(28);
        auto [f, _] = contract_.precompile_dispatch(msg_input);
        auto res = (contract_.*f)(msg_input, (sender), (value));
        post_call(res);
        return res;
    }
}
