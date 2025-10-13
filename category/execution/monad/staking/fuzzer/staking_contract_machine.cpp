#include <category/execution/monad/staking/fuzzer/staking_contract_machine.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>
#include <category/execution/monad/staking/util/test_util.hpp>

#include <algorithm>

using namespace monad::vm::fuzzing;

namespace monad::staking::test
{
    StakingContractMachine::StakingContractMachine(seed_t seed)
        : engine_{seed}
    {
        assert_all_invariants();
    }

    void StakingContractMachine::assert_all_invariants()
    {
        AssertState astate;

        auto tmp_valset_execution = model_.valset_execution();
        auto tmp_valset_execution_length = tmp_valset_execution.length();
        for (uint64_t i = 0; i < tmp_valset_execution_length; ++i) {
            auto const v = tmp_valset_execution.get(i).load().native();
            astate.valset_execution.insert(v);
        }

        auto tmp_valset_snapshot = model_.valset_snapshot();
        auto tmp_valset_snapshot_length = tmp_valset_snapshot.length();
        for (uint64_t i = 0; i < tmp_valset_snapshot_length; ++i) {
            auto const v = tmp_valset_snapshot.get(i).load().native();
            astate.valset_snapshot.insert(v);
        }

        auto tmp_valset_consensus = model_.valset_consensus();
        auto tmp_valset_consensus_length = tmp_valset_consensus.length();
        for (uint64_t i = 0; i < tmp_valset_consensus_length; ++i) {
            auto const v = tmp_valset_consensus.get(i).load().native();
            astate.valset_consensus.insert(v);
        }

        assert_valset_invariants(astate);
        assert_val_execution_invariants(astate);
        assert_delegator_invariants(astate);
        assert_accumulated_rewards_invariants(astate);
        assert_linked_list_invariants(astate);
        assert_solvency_invariants(astate);
    }

    void StakingContractMachine::assert_valset_invariants(
        AssertState const &astate)
    {
        auto const valset_execution_length =
            model_.valset_execution().length();
        auto const valset_snapshot_length =
            model_.valset_snapshot().length();
        auto const valset_consensus_length =
            model_.valset_consensus().length();

        // pairwise distinct elements:
        MONAD_ASSERT(
            astate.valset_execution.size() ==
            valset_execution_length);

        for (uint64_t v : astate.valset_execution) {
            MONAD_ASSERT(model_.val_execution(v).auth_address() != Address{});
        }

        // pairwise distinct elements:
        MONAD_ASSERT(
            astate.valset_consensus.size() ==
            valset_consensus_length);

        MONAD_ASSERT(valset_consensus_length <= ACTIVE_VALSET_SIZE);

        // pairwise distinct elements:
        MONAD_ASSERT(
            astate.valset_snapshot.size() ==
            valset_snapshot_length);

        MONAD_ASSERT(valset_snapshot_length <= ACTIVE_VALSET_SIZE);

        for (uint64_t v : astate.valset_consensus) {
            MONAD_ASSERT(astate.valset_execution.contains(v));
        }

        for_all_val_ids([&, this](u64_be v) {
            MONAD_ASSERT(
                astate.valset_consensus.contains(v.native()) ==
                model_.consensus_view(v).stake().load().native() >=
                    ACTIVE_VALIDATOR_STAKE);

            MONAD_ASSERT(
                astate.valset_snapshot.contains(v.native()) ==
                model_.snapshot_view(v).stake().load().native() >=
                    ACTIVE_VALIDATOR_STAKE);

            MONAD_ASSERT(
                model_.consensus_view(v).commission().load().native() <=
                MAX_COMMISSION);

            MONAD_ASSERT(
                model_.snapshot_view(v).commission().load().native() <=
                MAX_COMMISSION);

            auto const bit_bucket =
                model_.val_bitset_bucket(v).load().native();
            MONAD_ASSERT(
                !!(bit_bucket & (1 << (v.native() & 255))) ==
                astate.valset_execution.contains(v.native()));

            auto const current_stake =
                model_.val_execution(v).stake().load().native();
            auto const auth_stake =
                model_.delegator(v, model_.val_execution(v).auth_address())
                    .stake().load().native();
            MONAD_ASSERT(
                current_stake < ACTIVE_VALIDATOR_STAKE ||
                auth_stake < MIN_VALIDATE_STAKE ||
                astate.valset_execution.contains(v.native()));

            if (!model_.in_epoch_delay_period()) {
                MONAD_ASSERT(
                    model_.active_consensus_stake(v) ==
                    model_.consensus_view(v).stake().load().native());
                MONAD_ASSERT(
                    model_.active_consensus_commission(v) ==
                    model_.consensus_view(v).commission().load().native());
            }
            else {
                MONAD_ASSERT(
                    model_.active_consensus_stake(v) ==
                    model_.snapshot_view(v).stake().load().native());
                MONAD_ASSERT(
                    model_.active_consensus_commission(v) ==
                    model_.snapshot_view(v).commission().load().native());
            }
        });
    }

    void StakingContractMachine::assert_val_execution_invariants(
        AssertState const &)
    {
        for_all_val_ids([&, this](u64_be v) {
            MONAD_ASSERT(
                (v.native() == 0 || v.native() > model_.last_val_id()) ||
                model_.val_execution(v).auth_address() != Address{});

            MONAD_ASSERT(
                (v.native() > 0 && v.native() <= model_.last_val_id()) ||
                model_.val_execution(0).auth_address() == Address{});

            MONAD_ASSERT(
                v.native() == 0 ||
                model_.val_execution(
                    v.native() + 1).auth_address() == Address{} ||
                model_.val_execution(v).auth_address() != Address{});

            auto const auth_address =
                model_.val_execution(v).auth_address();
            auto const stake_sum =
                model_.delegator(v, auth_address)
                    .stake().load().native() +
                model_.delegator(v, auth_address)
                    .delta_stake().load().native() +
                model_.delegator(v, auth_address)
                    .next_delta_stake().load().native();
            MONAD_ASSERT(
                (v.native() == 0 || v.native() > model_.last_val_id()) ||
                (stake_sum >= MIN_VALIDATE_STAKE) ==
                !(model_.val_execution(v).get_flags() &
                  ValidatorFlagWithdrawn))

            MONAD_ASSERT(
                model_.val_execution(v).commission().load().native() <=
                MAX_COMMISSION);

            MONAD_ASSERT(model_.val_execution(v).get_flags() < 4);

            MONAD_ASSERT(
                (v.native() == 0 || v.native() > model_.last_val_id()) ||
                (model_.val_execution(v).stake().load().native() >=
                 ACTIVE_VALIDATOR_STAKE) ==
                !(model_.val_execution(v).get_flags() &
                  ValidatorFlagsStakeTooLow));

            if (enable_pubkey_assertions_) {
                auto const keys = model_.val_execution(v).keys().load();

                Secp256k1Pubkey const secp_pubkey{keys.secp_pubkey};
                if (secp_pubkey.is_valid()) {
                    MONAD_ASSERT(
                        v.native() > 0 &&
                        v.native() <= model_.last_val_id());
                    auto const secp_eth_address =
                        address_from_secpkey(secp_pubkey.serialize());
                    MONAD_ASSERT(model_.val_id(secp_eth_address) != 0);
                }
                else {
                    MONAD_ASSERT(
                        v.native() == 0 || v.native() > model_.last_val_id());
                }

                BlsPubkey const bls_pubkey{keys.bls_pubkey};
                if (bls_pubkey.is_valid()) {
                    MONAD_ASSERT(
                        v.native() > 0 &&
                        v.native() <= model_.last_val_id());
                    auto const bls_eth_address =
                        address_from_bls_key(bls_pubkey.serialize());
                    MONAD_ASSERT(model_.val_id_bls(bls_eth_address) != 0);
                }
                else {
                    MONAD_ASSERT(
                        v.native() == 0 || v.native() > model_.last_val_id());
                }
            }
        });
    }

    void StakingContractMachine::assert_delegator_invariants(
        AssertState const &)
    {
        for_all_val_ids_and_addresses([&, this](u64_be v, Address const &a) {
            auto del = model_.delegator(v, a);

            MONAD_ASSERT(
                del.next_delta_stake().load().native() == 0 ||
                del.next_delta_stake().load().native() >= DUST_THRESHOLD);

            MONAD_ASSERT(
                del.delta_stake().load().native() == 0 ||
                del.delta_stake().load().native() >= DUST_THRESHOLD);

            MONAD_ASSERT(
                del.stake().load().native() == 0 ||
                del.stake().load().native() >= DUST_THRESHOLD);

            MONAD_ASSERT(
                (del.next_delta_stake().load().native() == 0) ==
                (del.get_next_delta_epoch().native() == 0));

            MONAD_ASSERT(
                (del.delta_stake().load().native() == 0) ==
                (del.get_delta_epoch().native() == 0));

            MONAD_ASSERT(
                del.get_delta_epoch().native() == 0 ||
                del.get_next_delta_epoch().native() == 0 ||
                del.get_next_delta_epoch().native() ==
                    del.get_delta_epoch().native() + 1);

            MONAD_ASSERT(
                del.get_delta_epoch().native() <= model_.epoch() + 1);

            MONAD_ASSERT(
                del.get_next_delta_epoch().native() <= model_.epoch() + 2);

            // The invariant
            // withdrawal_request.amount = 0 iff withdrawal_request.epoch = 0
            // is slowing slowing down assert checking too much.
            // Instead just verify that the known withdrawal requests have
            // non-zero epoch and value.
            auto const &withdrawal_ids =
                model_.active_withdrawal_ids(v, a);
            for (uint8_t const i : withdrawal_ids) {
                std::cout << "i = " << (int)i << std::endl;
                std::cout << "v = " << v.native() << std::endl;
                std::cout << "a = " <<
                    intx::to_string(intx::be::load<uint256_t>(a)) << std::endl;
                // This is not part of the properties document.
                // It is used to sanity check the machine:
                std::tuple<uint64_t, Address, uint8_t> const key =
                    {v.native(), a, i};
                MONAD_ASSERT(all_withdrawal_requests_.contains(key));

                MONAD_ASSERT(
                    model_.withdrawal_request(v, a, i)
                        .load().amount.native() > 0);
                MONAD_ASSERT(
                    model_.withdrawal_request(v, a, i)
                        .load().epoch.native() > 0);
            }

            auto const error_bound = model_.error_bound();
            auto const unit_bias_rewards = model_.unit_bias_rewards(v, a);
            auto const pending_rewards = 
                model_.pending_rewards(v, a);
            auto const active_rewards =
                model_.delegator(v, a).rewards().load().native() +
                pending_rewards;
            MONAD_ASSERT(
                unit_bias_rewards <=
                (active_rewards + error_bound + 3 + 256) * UNIT_BIAS);
            MONAD_ASSERT(
                (active_rewards + error_bound + 3 + 256) * UNIT_BIAS <=
                unit_bias_rewards + ((error_bound + 3 + 256) * UNIT_BIAS));

            auto const this_epoch = model_.epoch();

            auto actual_delegator_stake = del.stake().load().native();
            if (del.get_delta_epoch().native() <= this_epoch) {
                actual_delegator_stake +=
                    del.delta_stake().load().native();
            }
            if (del.get_next_delta_epoch().native() <= this_epoch) {
                actual_delegator_stake +=
                    del.next_delta_stake().load().native();
            }
            MONAD_ASSERT(
                model_.delegator_stake(v, a, this_epoch) ==
                actual_delegator_stake);

            uint256_t actual_withdrawal_stake;
            for (uint8_t const i : withdrawal_ids) {
                auto withdrawal = model_.withdrawal_request(v, a, i).load();
                if (withdrawal.epoch.native() > this_epoch) {
                    actual_withdrawal_stake += withdrawal.amount.native();
                }
            }
            MONAD_ASSERT(
                model_.withdrawal_stake(v, a, this_epoch) ==
                actual_withdrawal_stake);
        });

        for_all_val_ids([&](u64_be v) {
            auto const epoch = model_.epoch();
            uint256_t del_stake_sum;
            uint256_t withdraw_stake_sum;
            for_all_addresses([&, this](Address const &a) {
                del_stake_sum +=
                    model_.delegator_stake(v, a, epoch);
                withdraw_stake_sum +=
                    model_.withdrawal_stake(v, a, epoch);
            });
            MONAD_ASSERT(
                model_.active_consensus_stake(v) == 0 ||
                model_.active_consensus_stake(v) ==
                del_stake_sum + withdraw_stake_sum);
        });
    }

    void StakingContractMachine::assert_accumulated_rewards_invariants(
        AssertState const &astate)
    {
        (void)astate;
    }

    void StakingContractMachine::assert_linked_list_invariants(
        AssertState const &astate)
    {
        (void)astate;
    }

    void StakingContractMachine::assert_solvency_invariants(
        AssertState const &astate)
    {
        (void)astate;
    }

    void StakingContractMachine::for_all_val_ids(
        std::function<void(u64_be)> f)
    {
        uint64_t n = model_.last_val_id() + 3;
        for (uint64_t i = 0; i < n; ++i) {
            f(i);
        }
    }

    void StakingContractMachine::for_all_addresses(
        std::function<void(Address const &)> f)
    {
        for (auto const &a : all_addresses_) {
            f(a);
        }
    }

    void StakingContractMachine::for_all_val_ids_and_addresses(
        std::function<void(u64_be, Address const &)> f)
    {
        for_all_val_ids([&](u64_be v){
            for_all_addresses([&](Address const &a) {
                f(v, a);
            });
        });
    }

    bool StakingContractMachine::transition(Transition t)
    {
        bool ok = true;
        switch (t)
        {
        case Transition::syscall_on_epoch_change:
            if (enable_trace_) {std::cout << "Transition::syscall_on_epoch_change" << std::endl;}
            syscall_on_epoch_change();
            break;
        case Transition::syscall_snapshot:
            if (enable_trace_) {std::cout << "Transition::syscall_snapshot" << std::endl;}
            syscall_snapshot();
            break;
        case Transition::syscall_reward:
            if (enable_trace_) {std::cout << "Transition::syscall_reward" << std::endl;}
            syscall_reward();
            break;
        case Transition::precompile_add_validator:
            if (enable_trace_) {std::cout << "Transition::precompile_add_validator" << std::endl;}
            precompile_add_validator();
            break;
        case Transition::precompile_delegate:
            if (enable_trace_) {std::cout << "Transition::precompile_delegate" << std::endl;}
            precompile_delegate();
            break;
        case Transition::precompile_undelegate:
            if (enable_trace_) {std::cout << "Transition::precompile_undelegate" << std::endl;}
            precompile_undelegate();
            break;
        case Transition::precompile_compound:
            if (enable_trace_) {std::cout << "Transition::precompile_compound" << std::endl;}
            ok = precompile_compound();
            break;
        case Transition::precompile_withdraw:
            if (enable_trace_) {std::cout << "Transition::precompile_withdraw" << std::endl;}
            ok = precompile_withdraw();
            break;
        case Transition::precompile_claim_rewards:
            if (enable_trace_) {std::cout << "Transition::precompile_claim_rewards" << std::endl;}
            precompile_claim_rewards();
            break;
        case Transition::precompile_change_commission:
            if (enable_trace_) {std::cout << "Transition::precompile_change_commission" << std::endl;}
            precompile_change_commission();
            break;
        case Transition::precompile_external_reward:
            if (enable_trace_) {std::cout << "Transition::precompile_external_reward" << std::endl;}
            ok = precompile_external_reward();
            break;
        case Transition::precompile_get_delegator:
            if (enable_trace_) {std::cout << "Transition::precompile_get_delegator" << std::endl;}
            precompile_get_delegator();
            break;
        default:
            MONAD_ABORT();
        }
        if (ok) {
            assert_all_invariants();
        }
        return ok;
    }

    void StakingContractMachine::skip_epochs(uint64_t const n)
    {
        if (n == 0) {
            return;
        }
        size_t i = 0;
        auto epoch = model_.epoch();
        if (epoch == 0 || model_.in_epoch_delay_period()) {
            ++i;
            auto const res = model_.syscall_on_epoch_change(++epoch);
            MONAD_ASSERT(res.has_value());
        }
        for (; i < n; ++i) {
            auto const res1 = model_.syscall_snapshot();
            MONAD_ASSERT(res1.has_value());
            auto const res2 = model_.syscall_on_epoch_change(++epoch);
            MONAD_ASSERT(res2.has_value());
        }
    }

    StakingContractMachine::seed_t StakingContractMachine::gen()
    {
        return engine_();
    }

    StakingContractMachine::Transition
    StakingContractMachine::gen_transition()
    {
        auto const x =
            gen() % static_cast<seed_t>(Transition::TRANSITION_COUNT);
        return static_cast<Transition>(x);
    }

    Address StakingContractMachine::gen_new_address()
    {
        auto const x = gen_uint256();
        Address a;
        std::memcpy(a.bytes, intx::as_bytes(x), sizeof(a.bytes));
        all_addresses_.push_back(a);
        return a;
    }

    Address StakingContractMachine::gen_old_address()
    {
        MONAD_ASSERT(!all_addresses_.empty());
        return all_addresses_[gen() % all_addresses_.size()];
    }

    Address StakingContractMachine::gen_new_or_old_address()
    {
        if (all_addresses_.empty()) {
            return gen_new_address();
        }
        return discrete_choice<Address>(
            engine_,
            [this](auto &) { return gen_new_address(); },
            Choice(0.80, [this](auto &) { return gen_old_address(); }));
    }

    std::pair<u64_be, Address>
    StakingContractMachine::gen_validator_auth_address()
    {
        auto const &v = validator_auth_addresses_;
        if (v.empty()) {
            auto const [signer, msg, secp, bls, sender, value] =
                gen_precompile_add_validator_input(
                    MIN_VALIDATE_STAKE, MAX_STAKE);
            model_precompile_add_validator(
                signer, msg, secp, bls, sender, value);
            MONAD_ASSERT(!validator_auth_addresses_.empty());
        }
        return validator_auth_addresses_[
            gen() % validator_auth_addresses_.size()];
    }

    u64_be StakingContractMachine::gen_delegable_val_id()
    {
        if (!delegable_val_ids_.empty()) {
            auto const v = delegable_val_ids_.sample(engine_);
            MONAD_ASSERT(model_.val_execution(v).exists());
            return v;
        }
        auto const [signer, msg, secp, bls, sender, value] =
            gen_precompile_add_validator_input(
                MIN_VALIDATE_STAKE, MAX_DELEGABLE_STAKE);
        auto const v = model_precompile_add_validator(
            signer, msg, secp, bls, sender, value);
        MONAD_ASSERT(model_.val_execution(v).exists());
        return v;
    }

    u64_be StakingContractMachine::gen_potential_val_id()
    {
        if (all_val_ids_.empty()) {
            return gen();
        }
        return discrete_choice<u64_be>(
            engine_,
            [this](auto &) { return gen(); },
            Choice(0.50, [this](auto &) {
                return all_val_ids_[gen() % all_val_ids_.size()]; }));
    }

    std::pair<u64_be, Address> StakingContractMachine::gen_delegator()
    {
        if (all_delegators_.empty()) {
            auto const [signer, msg, secp, bls, sender, value] =
                gen_precompile_add_validator_input(
                    MIN_VALIDATE_STAKE, MAX_STAKE);
            model_precompile_add_validator(
                signer, msg, secp, bls, sender, value);
            MONAD_ASSERT(!all_delegators_.empty());
        }
        auto const &[v, a] = all_delegators_.sample(engine_);
        return {u64_be{v}, a};
    }

    uint256_t StakingContractMachine::gen_uint256()
    {
        return uint256_t{gen(), gen(), gen(), gen()};
    }

    uint256_t StakingContractMachine::gen_bound_biased_uint256(
        uint256_t lower_bound, uint256_t upper_bound)
    {
        MONAD_ASSERT(lower_bound <= upper_bound);
        return discrete_choice<uint256_t>(
            engine_,
            [&, this](auto &) {
                auto const x = gen_uint256();
                auto const m = upper_bound - lower_bound + 1;
                return m ? lower_bound + x % m : x;
            },
            Choice(0.02, [&](auto &) {
                auto const x = gen_uint256();
                auto const m =
                    1 +
                    std::min(upper_bound - lower_bound, 2 * DUST_THRESHOLD);
                return m ? lower_bound + x % m : x;
            }),
            Choice(0.02, [&](auto &) {
                auto const x = gen_uint256();
                auto const m =
                    1 +
                    std::min(upper_bound - lower_bound, 2 * DUST_THRESHOLD);
                return m ? upper_bound - x % m : x;
            }),
            Choice(0.02, [&](auto &) {
                return lower_bound == upper_bound
                    ? lower_bound
                    : lower_bound + 1;
            }),
            Choice(0.02, [&](auto &) {
                return lower_bound == upper_bound
                    ? upper_bound
                    : upper_bound - 1;
            }),
            Choice(0.02, [&](auto &) { return lower_bound; }),
            Choice(0.02, [&](auto &) { return upper_bound; }));
    }

    Address StakingContractMachine::gen_delegator_to_val_id(u64_be val_id)
    {
        MONAD_ASSERT(model_.val_execution(val_id).exists());
        auto ds = model_.get_delegators_for_validator(val_id);
        MONAD_ASSERT(!ds.empty());
        return ds[gen() & ds.size()];
    }

    std::optional<u64_be>
    StakingContractMachine::gen_active_consensus_val_id()
    {
        auto const valset = model_.in_epoch_delay_period()
            ? model_.valset_snapshot()
            : model_.valset_consensus();
        auto const n = valset.length();
        if (n == 0) {
            return std::nullopt;
        }
        return valset.get(gen() % n).load().native();
    }

    void StakingContractMachine::syscall_on_epoch_change()
    {
        uint64_t next_epoch{};
        if (model_.epoch() == 0) {
            next_epoch = 1 + gen() % 1'000'000;
            auto const res = model_.syscall_on_epoch_change(next_epoch);
            MONAD_ASSERT(res.has_value());
        }
        else {
            next_epoch = model_.epoch() + 1;
            if (!model_.in_epoch_delay_period()) {
                auto const res = model_.syscall_snapshot();
                MONAD_ASSERT(res.has_value());
            }
            auto const res =
                model_.syscall_on_epoch_change(next_epoch);
            MONAD_ASSERT(res.has_value());
        }

        // Post conditions:

        MONAD_ASSERT(!model_.in_epoch_delay_period());

        MONAD_ASSERT(model_.epoch() == next_epoch);

        for_all_val_ids([&](u64_be v) {
            MONAD_ASSERT(
                model_.active_consensus_stake(v) ==
                model_.consensus_view(v).stake().load().native());
        });
    }

    void StakingContractMachine::syscall_snapshot()
    {
        if (model_.epoch() == 0) {
            return;
        }
        if (model_.in_epoch_delay_period()) {
            auto const res =
                model_.syscall_on_epoch_change(model_.epoch() + 1);
            MONAD_ASSERT(res.has_value());
        }
        auto const res = model_.syscall_snapshot();
        MONAD_ASSERT(res.has_value());
    }

    void StakingContractMachine::syscall_reward()
    {
        if (auto const val_id = gen_active_consensus_val_id()) {
            auto const signer = val_id_to_signer_.at(val_id->native());
            auto const reward =
                gen_bound_biased_uint256(0, 1'000'000 * MON);
            auto const res = model_.syscall_reward(signer, reward);
            MONAD_ASSERT(res.has_value());
        }
    }

    Address
    StakingContractMachine::get_add_validator_message_auth_address(
        byte_string const &msg)
    {
        Address a;
        std::memcpy(a.bytes, &msg[81], sizeof(a.bytes));
        return a;
    }

    std::tuple<
        Address,
        byte_string,
        byte_string,
        byte_string,
        Address,
        evmc_uint256be>
    StakingContractMachine::gen_precompile_add_validator_input(
        uint256_t const &min_stake, uint256_t const &max_stake)
    {
        MONAD_ASSERT(min_stake >= MIN_VALIDATE_STAKE);
        MONAD_ASSERT(max_stake >= min_stake);
        MONAD_ASSERT(max_stake <= MAX_STAKE);

        Address const sender = gen_new_or_old_address();
        uint256_t const stake =
            gen_bound_biased_uint256(min_stake, max_stake);
        auto const value = intx::be::store<evmc_uint256be>(stake);
        Address const auth_address = gen_new_or_old_address();
        auto const commission = gen_bound_biased_uint256(0, MAX_COMMISSION);
        auto const secret = intx::be::store<evmc::bytes32>(gen_uint256());

        auto [msg, secp, bls, signer] = craft_add_validator_input_raw(
            auth_address, stake, commission, secret);

        return {signer, msg, secp, bls, sender, value};
    }

    u64_be StakingContractMachine::model_precompile_add_validator(
        Address const &signer,
        byte_string const &msg,
        byte_string const &secp,
        byte_string const &bls,
        Address const &sender,
        evmc_uint256be const &value)
    {
        auto result = model_.precompile_add_validator(
            msg, secp, bls, sender, value);
        MONAD_ASSERT(result.has_value());

        auto const val_id = result.value();

        all_val_ids_.push_back(val_id);
        if (intx::be::load<uint256_t>(value.bytes) <= MAX_DELEGABLE_STAKE) {
            MONAD_ASSERT(model_.val_execution(val_id).exists());
            auto const ins = delegable_val_ids_.insert(val_id.native());
            MONAD_ASSERT(ins);
        }

        auto const auth_address =
            get_add_validator_message_auth_address(msg);

        auto ins1 = all_delegators_.insert({val_id.native(), auth_address});
        MONAD_ASSERT(ins1);

        auto [_, ins2] = val_id_to_signer_.insert({val_id.native(), signer});
        MONAD_ASSERT(ins2);

        validator_auth_addresses_.emplace_back(val_id, auth_address);

        return val_id;
    }

    void StakingContractMachine::precompile_add_validator()
    {
        auto const [signer, msg, secp, bls, sender, value] =
            gen_precompile_add_validator_input(MIN_VALIDATE_STAKE, MAX_STAKE);

        auto const v = model_precompile_add_validator(
            signer, msg, secp, bls, sender, value);
        (void)v;
    }

    std::tuple<u64_be, Address, evmc_uint256be>
    StakingContractMachine::gen_precompile_delegate_input()
    {
        auto const &sender = gen_new_or_old_address();
        using R = std::tuple<u64_be, Address, evmc_uint256be>;
        return discrete_choice<R>(
            engine_,
            [&, this](auto &) -> R {
                auto const val_id = gen_delegable_val_id();
                auto const val_stake =
                    model_.val_execution(val_id).stake().load().native();
                MONAD_ASSERT(val_stake <= MAX_DELEGABLE_STAKE);
                auto const del_stake = gen_bound_biased_uint256(
                    MIN_DELEGATE_STAKE,
                    MAX_STAKE - val_stake);
                auto const value =
                    intx::be::store<evmc_uint256be>(del_stake);
                return {val_id, sender, value};
            },
            Choice(0.01, [&, this](auto &) -> R {
                return {gen_potential_val_id(), sender, evmc_uint256be{}};
            }));
    }

    void StakingContractMachine::model_precompile_delegate(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        auto result = model_.precompile_delegate(val_id, sender, value);
        MONAD_ASSERT(result.has_value());

        if (intx::be::load<uint256_t>(value) == 0) {
            return;
        }

        auto const val_stake =
            model_.val_execution(val_id).stake().load().native();
        if (val_stake > MAX_DELEGABLE_STAKE) {
            auto const er = delegable_val_ids_.erase(val_id.native());
            MONAD_ASSERT(er);
        }
        all_delegators_.insert({val_id.native(), sender});
    }

    void StakingContractMachine::precompile_delegate()
    {
        auto const [val_id, sender, value] = gen_precompile_delegate_input();

        model_precompile_delegate(val_id, sender, value);
    }

    std::optional<std::tuple<
        u64_be, u256_be, u8_be, Address, evmc_uint256be>>
    StakingContractMachine::gen_precompile_undelegate_input(
        uint256_t const &min_undelegate)
    {
        u64_be val_id;
        Address sender;
        uint256_t del_stake;

        for (size_t i = 0; i < 10; ++i) {
            std::tie(val_id, sender) = gen_delegator();
            del_stake =
                model_.delegator(val_id, sender).stake().load().native();
            if (del_stake >= min_undelegate) {
                break;
            }
        }
        if (del_stake < min_undelegate) {
            return std::nullopt;
        }

        std::tuple<uint64_t, uint256_t> key =
            {val_id.native(), intx::be::load<uint256_t>(sender.bytes)};
        auto wis = available_withdrawal_ids_.find(key);

        if (wis != available_withdrawal_ids_.end() && wis->second.empty()) {
            auto const [signer, msg, secp, bls, asender, avalue] =
                gen_precompile_add_validator_input(
                    MIN_VALIDATE_STAKE, MAX_DELEGABLE_STAKE);
            val_id = model_precompile_add_validator(
                signer, msg, secp, bls, asender, avalue);
            sender = get_add_validator_message_auth_address(msg);
            wis = available_withdrawal_ids_.end();
            key = {val_id.native(), intx::be::load<uint256_t>(sender.bytes)};
            del_stake =
                model_.delegator(val_id, sender).stake().load().native();
        }

        if (wis == available_withdrawal_ids_.end()) {
            std::vector<u8_be> wi;
            wi.reserve(256);
            for (size_t i = 0; i < 256; ++i) {
                wi.emplace_back(static_cast<uint8_t>(i));
            }
            auto const [it, _] =
                available_withdrawal_ids_.insert({key, std::move(wi)});
            wis = it;
        }

        auto &wi = wis->second;
        MONAD_ASSERT(!wi.empty());

        auto const w = wi[gen() % wi.size()];

        auto const undelegate_stake =
            gen_bound_biased_uint256(min_undelegate, del_stake);

        return {{val_id, undelegate_stake, w, sender, evmc_uint256be{}}};
    }

    void StakingContractMachine::model_precompile_undelegate(
        u64_be val_id, u256_be stake, u8_be wid,
        Address const &sender, evmc_uint256be const &value)
    {
        MONAD_ASSERT(model_.val_execution(val_id).exists());

        auto result = model_.precompile_undelegate(
            val_id, stake, wid, sender, value);
        MONAD_ASSERT(result.has_value());

        if (stake.native() == 0) {
            return;
        }

        std::tuple<uint64_t, uint256_t> const key =
            {val_id.native(), intx::be::load<uint256_t>(sender.bytes)};
        auto wis = available_withdrawal_ids_.find(key);
        auto const pos =
            std::find(wis->second.begin(), wis->second.end(), wid);
        MONAD_ASSERT(pos != wis->second.end());
        wis->second.erase(pos);

        auto const ins = all_withdrawal_requests_.insert(
            {val_id.native(), sender, wid.native()});
        MONAD_ASSERT(ins);

        auto const del_stake =
            model_.delegator(val_id, sender).stake().load().native();
        if (del_stake == 0) {
            auto const er = all_delegators_.erase({val_id.native(), sender});
            MONAD_ASSERT(er);
        }
        auto const val_stake =
            model_.val_execution(val_id).stake().load().native();
        if (val_stake <= MAX_DELEGABLE_STAKE) {
            delegable_val_ids_.insert(val_id.native());
        }
    }

    void StakingContractMachine::precompile_undelegate()
    {
        auto const input = gen_precompile_undelegate_input(0);
        MONAD_ASSERT(input.has_value());
        auto const [val_id, stake, wid, sender, value] = *input;
        model_precompile_undelegate(val_id, stake, wid, sender, value);
    }

    std::optional<std::tuple<u64_be, Address, evmc_uint256be>>
    StakingContractMachine::gen_precompile_compound_input()
    {
        u64_be val_id;
        Address sender;
        uint256_t rewards;
        with_probability(engine_, 0.005, [&](auto &) {
            // Small probability of arbitrary val_id and sender
            val_id = gen() % (model_.last_val_id() + 3);
            sender = gen_new_or_old_address();
            rewards =
                model_.delegator(val_id, sender).rewards().load().native() +
                model_.unaccumulated_rewards(val_id, sender);
        });
        if (sender != Address{}) {
            auto const val_stake =
                model_.val_execution(val_id).stake().load().native();
            if (val_stake + rewards <= MAX_STAKE &&
                (rewards == 0 || rewards >= MIN_DELEGATE_STAKE)) {
                return {{val_id, sender, evmc_uint256be{}}};
            }
        }
        // Try a few times to find a suitable delegator
        for (size_t iters = 0; iters < 10; ++iters) {
            std::tie(val_id, sender) = gen_delegator();
            rewards =
                model_.delegator(val_id, sender).rewards().load().native() +
                model_.unaccumulated_rewards(val_id, sender);
            if (rewards == 0) {
                return {{val_id, sender, evmc_uint256be{}}};
            }
            if (rewards >= MIN_DELEGATE_STAKE) {
                auto const val_stake =
                    model_.val_execution(val_id).stake().load().native();
                if (val_stake + rewards <= MAX_STAKE) {
                    return {{val_id, sender, evmc_uint256be{}}};
                }
            }
        }
        return std::nullopt;
    }

    void StakingContractMachine::model_precompile_compound(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        uint256_t const rewards =
            model_.delegator(val_id, sender).rewards().load().native() +
            model_.unaccumulated_rewards(val_id, sender);

        auto const res = model_.precompile_compound(val_id, sender, value);
        MONAD_ASSERT(res.has_value());

        if (rewards == 0) {
            return;
        }

        auto const val_stake =
            model_.val_execution(val_id).stake().load().native();
        MONAD_ASSERT(val_stake <= MAX_STAKE);
        if (val_stake > MAX_DELEGABLE_STAKE) {
            auto const er = delegable_val_ids_.erase(val_id.native());
            MONAD_ASSERT(er);
        }
    }

    bool StakingContractMachine::precompile_compound()
    {
        auto const input = gen_precompile_compound_input();
        if (!input.has_value()) {
            return false;
        }
        auto const [val_id, sender, value] = *input;
        model_precompile_compound(val_id, sender, value);
        return true;
    }

    std::optional<std::tuple<u64_be, u8_be, Address, evmc_uint256be>>
    StakingContractMachine::gen_precompile_withdraw_input()
    {
        if (all_withdrawal_requests_.empty()) {
            auto const input = gen_precompile_undelegate_input(1);
            if (!input.has_value()) {
                return std::nullopt;
            }
            auto const [val_id, stake, wid, sender, value] = *input;
            model_precompile_undelegate(val_id, stake, wid, sender, value);
            MONAD_ASSERT(!all_withdrawal_requests_.empty());
        }
        auto const [pre_val_id, sender, pre_wid] =
            all_withdrawal_requests_.sample(engine_);
        u64_be const val_id = pre_val_id;
        u8_be const wid = pre_wid;

        auto const wit =
            model_.withdrawal_request(val_id, sender, wid).load();
        auto const wepoch = wit.epoch.native() + WITHDRAWAL_DELAY;
        auto const epoch = model_.epoch();
        if (epoch < wepoch) {
            skip_epochs(wepoch - epoch);
        }
        return {{val_id, wid, sender, evmc_uint256be{}}};
    }

    void StakingContractMachine::model_precompile_withdraw(
        u64_be val_id,
        u8_be wid,
        Address const &sender,
        evmc_uint256be const &value)
    {
        auto result = model_.precompile_withdraw(val_id, wid, sender, value);
        MONAD_ASSERT(result.has_value());

        std::tuple<uint64_t, uint256_t> const k1 =
            {val_id.native(), intx::be::load<uint256_t>(sender.bytes)};
        available_withdrawal_ids_.at(k1).push_back(wid);

        auto const er = all_withdrawal_requests_.erase(
            {val_id.native(), sender, wid.native()});
        MONAD_ASSERT(er);
    }

    bool StakingContractMachine::precompile_withdraw()
    {
        auto const input = gen_precompile_withdraw_input();
        if (!input.has_value()) {
            return false;
        }
        auto const [val_id, wid, sender, value] = *input;
        model_precompile_withdraw(val_id, wid, sender, value);
        return true;
    }

    std::tuple<u64_be, Address, evmc_uint256be>
    StakingContractMachine::gen_precompile_claim_rewards_input()
    {
        u64_be val_id;
        Address sender;
        with_probability(engine_, 0.005, [&](auto &) {
            // Small probability of arbitrary val_id and sender
            val_id = gen() % (model_.last_val_id() + 3);
            sender = gen_new_or_old_address();
        });
        if (sender != Address{}) {
            return {val_id, sender, evmc_uint256be{}};
        }
        std::tie(val_id, sender) = gen_delegator();
        return {val_id, sender, evmc_uint256be{}};
    }

    void StakingContractMachine::model_precompile_claim_rewards(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        auto const res = model_.precompile_claim_rewards(
            val_id, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    void StakingContractMachine::precompile_claim_rewards()
    {
        auto const [val_id, sender, value] =
            gen_precompile_claim_rewards_input();
        model_precompile_claim_rewards(val_id, sender, value);
    }

    std::tuple<u64_be, u256_be, Address, evmc_uint256be>
    StakingContractMachine::gen_precompile_change_commission_input()
    {
        auto const [val_id, sender] = gen_validator_auth_address();
        auto const commission = gen_bound_biased_uint256(0, MAX_COMMISSION);
        return {val_id, commission, sender, evmc_uint256be{}};
    }

    void StakingContractMachine::model_precompile_change_commission(
        u64_be val_id,
        u256_be const &commission,
        Address const &sender,
        evmc_uint256be const &value)
    {
        auto const res = model_.precompile_change_commission(
            val_id, commission, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    void StakingContractMachine::precompile_change_commission()
    {
        auto const [val_id, commission, sender, value] =
            gen_precompile_change_commission_input();
        model_precompile_change_commission(
            val_id, commission, sender, value);
    }

    std::optional<std::tuple<u64_be, Address, evmc_uint256be>>
    StakingContractMachine::gen_precompile_external_reward_input()
    {
        if (auto const val_id = gen_active_consensus_val_id()) {
            auto const sender = gen_new_or_old_address();
            auto const reward = gen_bound_biased_uint256(
                MIN_EXTERNAL_REWARD, MAX_EXTERNAL_REWARD);
            auto const value = intx::be::store<evmc_uint256be>(reward);
            return {{*val_id, sender, value}};
        }
        return std::nullopt;
    }

    void StakingContractMachine::model_precompile_external_reward(
        u64_be val_id, Address const &sender, evmc_uint256be const &value)
    {
        auto const res = model_.precompile_external_reward(
            val_id, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    bool StakingContractMachine::precompile_external_reward()
    {
        auto const input = gen_precompile_external_reward_input();
        if (!input.has_value()) {
            return false;
        }
        auto const [val_id, sender, value] = *input;
        model_precompile_external_reward(val_id, sender, value);
        return true;
    }

    std::tuple<u64_be, Address, Address, evmc_uint256be>
    StakingContractMachine::gen_precompile_get_delegator_input()
    {
        using R = std::tuple<u64_be, Address, Address, evmc_uint256be>;
        return discrete_choice<R>(
            engine_,
            [&, this](auto &) -> R {
                auto const [val_id, addr] = gen_delegator();
                auto const sender = gen_new_or_old_address();
                return {val_id, addr, sender, evmc_uint256be{}};
            },
            Choice(0.05, [&, this](auto &) -> R {
                auto const val_id = gen() % (model_.last_val_id() + 3);
                auto const addr = gen_new_or_old_address();
                auto const sender = gen_new_or_old_address();
                return {val_id, addr, sender, evmc_uint256be{}};
            }));
    }

    void StakingContractMachine::model_precompile_get_delegator(
        u64_be val_id,
        Address const &addr,
        Address const &sender,
        evmc_uint256be const &value)
    {
        auto const res = model_.precompile_get_delegator(
            val_id, addr, sender, value);
        MONAD_ASSERT(res.has_value());
    }

    void StakingContractMachine::precompile_get_delegator()
    {
        auto const [val_id, addr, sender, value] =
            gen_precompile_get_delegator_input();
        model_precompile_get_delegator(val_id, addr, sender, value);
    }
}
