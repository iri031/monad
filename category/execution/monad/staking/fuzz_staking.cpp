// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>
#include <category/execution/monad/staking/util/staking_error.hpp>
#include <category/execution/monad/staking/util/test_helpers.hpp>
#include <category/vm/vm.hpp>

#include <cstdint>
#include <list>
#include <memory>
#include <optional>
#include <ranges>
#include <set>
#include <unordered_map>
#include <unordered_set>

#include <blst.h>
#include <boost/functional/hash.hpp>
#include <boost/outcome/success_failure.hpp>
#include <fuzzer/FuzzedDataProvider.h>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <secp256k1.h>

#include <quill/Quill.h>

using namespace monad::staking::test;
using namespace monad::staking;
using namespace monad;

// FuzzedDataProvider.ConsumeIntegralInRange<T> doesn't support types that
// exceed u64
uint256_t consume_u256_in_range(
    FuzzedDataProvider &provider, uint256_t const &lo, uint256_t const &hi)
{
    MONAD_ASSERT(hi >= lo);
    auto const bytes = provider.ConsumeBytes<uint8_t>(32); // may be shorter
    uint256_t x = 0;
    for (uint8_t const c : bytes) {
        x = (x << 8) | c;
    }
    uint256_t const span = hi - lo + 1;
    if (span == 0) {
        return lo + x;
    }
    return lo + (x % span);
}

// A simplified implementation of the staking contract in memory. Uses different
// data structure approaches which should match the staking contract. The Oracle
// contract only verifies "user visible" states. It therefore does not verify
// accumulators, the execution set, etc. It only looks at the consensus sets,
// the snapshot sets, active stake, and rewards.
class StakingOracle
{

    struct DelegatorOracle
    {
        uint64_t val_id;
        Address address;
        uint256_t active_stake;
        uint256_t delta_stake;
        uint256_t next_delta_stake;
        uint256_t rewards;
    };

    struct DelegatorHash
    {
        std::size_t
        operator()(std::pair<uint64_t, Address> const &key) const noexcept
        {
            std::size_t seed = 0;
            boost::hash_combine(seed, key.first);
            boost::hash_combine(
                seed,
                boost::hash_range(
                    std::begin(key.second.bytes), std::end(key.second.bytes)));

            return seed;
        }
    };

    struct ConsensusViewOracle
    {
        uint64_t id;
        uint256_t stake;
    };

    struct ValidatorOracle
    {
        uint64_t id;
        Address auth_address;
        uint256_t stake;
        uint256_t commission;
        uint256_t rewards_per_token;
        uint64_t flags;

        bool operator<(ValidatorOracle const &other) const
        {
            bool ourflags = (flags != 0);
            bool theirflags = (other.flags != 0);
            if (ourflags != theirflags) {
                return ourflags < theirflags; // non-zero flags at the bottom
            }
            if (stake != other.stake) {
                return stake > other.stake; // larger stake first
            }
            return id > other.id; // then larger id
        }
    };

    using ExecutionValidatorSet = std::set<ValidatorOracle>;
    using DelegatorStorage = std::list<DelegatorOracle>;
    using ConsensusValidatorSet = std::list<ConsensusViewOracle>;

    using ExecutionValidatorHandle = ExecutionValidatorSet::iterator;
    using ConsensusValidatorHandle = ConsensusValidatorSet::iterator;
    using DelegatorHandle = DelegatorStorage::iterator;

    // execution view

    // validators
    uint64_t last_validator_id = 0;
    std::unordered_set<bytes32_t> used_secrets;
    uint64_t epoch = 0;
    bool in_epoch_delay_period = false;

    ExecutionValidatorSet execution_validator_set{};
    std::unordered_map<uint64_t, ExecutionValidatorHandle>
        execution_validator_map;

    // delegators
    DelegatorStorage delegators{};
    std::unordered_map<
        std::pair<uint64_t, Address>, DelegatorHandle, DelegatorHash>
        delegator_map;

    // consensus view
    ConsensusValidatorSet consensus_validator_set;
    ConsensusValidatorSet snapshot_validator_set;

    std::unordered_map<uint64_t, ConsensusValidatorHandle>
        consensus_validator_map;
    std::unordered_map<uint64_t, ConsensusValidatorHandle>
        snapshot_validator_map;

    std::optional<ValidatorOracle> pop_validator(uint64_t const val_id)
    {
        auto it = execution_validator_map.find(val_id);
        if (it == execution_validator_map.end()) {
            return std::nullopt;
        }

        ExecutionValidatorHandle handle = it->second;
        ValidatorOracle validator = *handle;

        execution_validator_set.erase(handle);
        execution_validator_map.erase(it);
        return validator;
    }

    void insert_validator(ValidatorOracle &&validator)
    {
        auto [it, ok] = execution_validator_set.emplace(std::move(validator));
        MONAD_ASSERT(ok);
        execution_validator_map.try_emplace(it->id, it);
    }

public:
    bool is_in_epoch_delay_period() const
    {
        return in_epoch_delay_period;
    }

    uint64_t get_epoch() const
    {
        return epoch;
    }

    ////////////////////
    // Fuzzer actions //
    ////////////////////
    Result<void> add_validator(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission, bytes32_t const &secret)
    {
        auto [_, inserted] = used_secrets.emplace(secret);
        if (!inserted /* duplicate keys not allowed */) {
            return StakingError::ValidatorExists;
        }

        uint64_t validator_id = last_validator_id + 1;

        insert_validator(ValidatorOracle{
            .id = validator_id,
            .auth_address = auth_address,
            .stake = 0, /* updated in delegate */
            .commission = commission,
            .rewards_per_token = 0,
            .flags = ValidatorFlagsStakeTooLow, /* updated in delegate if
                                                appropriate */
        });
        BOOST_OUTCOME_TRY(delegate(validator_id, auth_address, stake));

        ++last_validator_id;

        return outcome::success();
    }

    Result<void> delegate(
        uint64_t const val_id, Address const &sender, uint256_t const &stake)
    {
        // validator updates
        auto validator = pop_validator(val_id);
        if (!validator.has_value()) {
            return StakingError::UnknownValidator;
        }

        // The contract checks existence on nonzero auth address
        if (validator->auth_address == Address{}) {
            return StakingError::UnknownValidator;
        }

        validator->stake += stake;

        if (validator->stake >= ACTIVE_VALIDATOR_STAKE) {
            validator->flags = validator->flags & ~ValidatorFlagsStakeTooLow;
        }

        if (validator->auth_address == sender &&
            validator->stake >= MIN_VALIDATE_STAKE) {
            validator->flags = validator->flags & ~ValidatorFlagWithdrawn;
        }
        insert_validator(std::move(validator.value()));

        // delegator updates
        auto delegator_key = std::make_pair(val_id, sender);
        if (delegator_map.find(delegator_key) == delegator_map.end()) {
            auto delegator_it = delegators.insert(
                delegators.end(),
                DelegatorOracle{
                    .val_id = val_id,
                    .address = sender,
                    .active_stake = 0,
                    .delta_stake = 0,
                    .next_delta_stake = 0,
                    .rewards = 0});
            auto [_, inserted] =
                delegator_map.try_emplace(delegator_key, delegator_it);
            MONAD_ASSERT(inserted);
        }
        auto delegator_it = delegator_map.find(delegator_key);
        MONAD_ASSERT(delegator_it != delegator_map.end());
        DelegatorHandle delegator = delegator_it->second;

        if (!is_in_epoch_delay_period()) {
            delegator->delta_stake += stake;
        }
        else {
            delegator->next_delta_stake += stake;
        }

        return outcome::success();
    }

    void snapshot()
    {
        // swap consensus view to snapshot view
        snapshot_validator_set = std::move(consensus_validator_set);
        snapshot_validator_map = std::move(consensus_validator_map);
        consensus_validator_set.clear();
        consensus_validator_map.clear();

        // rebuild consensus view from execution view.  take top N validators.
        // valset is a max heap, so just iterate that.
        auto it = execution_validator_set.begin();
        uint64_t count = 0;
        for (;
             it != execution_validator_set.end() && count < ACTIVE_VALSET_SIZE;
             ++it, ++count) {

            if (it->flags != ValidatorFlagsOk) {
                // validators with flags are at the bottom of the heap. they
                // aren't candidates, so break out.
                break;
            }
            ConsensusValidatorHandle handle = consensus_validator_set.insert(
                consensus_validator_set.end(),
                ConsensusViewOracle{.id = it->id, .stake = it->stake});
            consensus_validator_map[it->id] = handle;
        }

        in_epoch_delay_period = true;
    }

    void epoch_change()
    {
        // update all delegator stakes
        for (DelegatorOracle &delegator : delegators) {
            delegator.active_stake += delegator.delta_stake;
            delegator.delta_stake = delegator.next_delta_stake;
            delegator.next_delta_stake = 0;
        }

        in_epoch_delay_period = false;
        epoch += 1;
    }

    //////////////////////
    // Verify Functions //
    //////////////////////

    void verify_after_snapshot(StakingContract &contract)
    {
        MONAD_ASSERT(
            contract.vars.in_epoch_delay_period.load_checked().has_value());

        // consensus set
        MONAD_ASSERT(
            contract.vars.valset_consensus.length() ==
            consensus_validator_set.size());
        for (auto const &&[i, cv] :
             std::views::enumerate(consensus_validator_set)) {
            uint64_t contract_id =
                contract.vars.valset_consensus.get(static_cast<uint64_t>(i))
                    .load()
                    .native();
            uint256_t contract_stake =
                contract.vars.consensus_stake(contract_id).load().native();

            MONAD_ASSERT(contract_id == cv.id);
            MONAD_ASSERT(contract_stake == cv.stake);
        }

        // snapshot set
        MONAD_ASSERT(
            contract.vars.valset_snapshot.length() ==
            snapshot_validator_set.size());
        for (auto const &&[i, sv] :
             std::views::enumerate(snapshot_validator_set)) {
            uint64_t contract_id =
                contract.vars.valset_snapshot.get(static_cast<uint64_t>(i))
                    .load()
                    .native();
            uint256_t contract_stake =
                contract.vars.snapshot_stake(contract_id).load().native();

            MONAD_ASSERT(contract_id == sv.id);
            MONAD_ASSERT(contract_stake == sv.stake);
        }
    }

    void verify_after_epoch_change(StakingContract &contract)
    {
        MONAD_ASSERT(contract.vars.epoch.load().native() == epoch);

        for (DelegatorOracle const &oracle_delegator : delegators) {
            // pull delegator up to date
            byte_string const input = craft_get_delegator_input(
                oracle_delegator.val_id, oracle_delegator.address);
            MONAD_ASSERT(
                !contract.precompile_get_delegator(input, {}, {}).has_error());

            // check stake
            auto contract_delegator = contract.vars.delegator(
                oracle_delegator.val_id, oracle_delegator.address);
            MONAD_ASSERT(
                contract_delegator.stake().load().native() ==
                oracle_delegator.active_stake);
        }
    }
};

extern "C" int LLVMFuzzerTestOneInput(uint8_t const *input, size_t const size)
{
    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Error);

    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};

    FuzzedDataProvider provider{input, size};

    BlockHeader header{.number = 0};
    StakingOracle oracle;

    enum UserTransaction : uint32_t
    {
        ADD_VALIDATOR = 0,
        DELEGATE,
        // UNDELEGATE,
        kMaxValue, /* For the fuzzed data provider */
    };

    bytes32_t parent_block_id{};
    while (provider.remaining_bytes() > 0) {
        if (header.number > 0) {
            tdb.set_block_and_prefix(header.number - 1, parent_block_id);
        }
        BlockState bs{tdb, vm};
        {
            State state{bs, Incarnation{header.number, 0}};
            StakingContract contract(state);
            state.add_to_balance(
                STAKING_CA, 0); // creates staking account in state

            // Maybe perform a state change?
            if (provider.ConsumeProbability<float>() < 0.2) {
                if (!oracle.is_in_epoch_delay_period()) {
                    oracle.snapshot();
                    MONAD_ASSERT(!contract.syscall_snapshot({}).has_error());
                    oracle.verify_after_snapshot(contract);
                }
                else {
                    oracle.epoch_change();
                    u64_be const epoch = oracle.get_epoch();
                    byte_string_view input{epoch.bytes, sizeof(u64_be)};
                    MONAD_ASSERT(
                        !contract.syscall_on_epoch_change(input).has_error());
                    oracle.verify_after_epoch_change(contract);
                }
            }
            MONAD_ASSERT(bs.can_merge(state));
            bs.merge(state);
        }

        // TODO: Reward

        // Fuzz a user transaction
        State state{bs, Incarnation{header.number, 1}};
        StakingContract contract(state);
        bool user_txn_success = true;
        state.push();
        auto const action = provider.ConsumeEnum<UserTransaction>();
        switch (action) {
        case ADD_VALIDATOR: {
            // Read in data
            Address auth_address;
            bytes32_t secret;
            provider.ConsumeData(auth_address.bytes, sizeof(Address));
            provider.ConsumeData(secret.bytes, sizeof(bytes32_t));

            // verify it.
            if (!is_secp_secret_valid(secret)) {
                break;
            }

            uint256_t const stake = consume_u256_in_range(
                provider, MIN_VALIDATE_STAKE, ACTIVE_VALIDATOR_STAKE);
            uint256_t const commission =
                consume_u256_in_range(provider, 0, MON);

            // add validator to staking contract
            auto [input, _] = craft_add_validator_input(
                auth_address, stake, commission, secret);
            state.add_to_balance(STAKING_CA, stake);
            auto const msg_value = intx::be::store<evmc_uint256be>(stake);

            // add validator to oracle
            auto const oracle_res =
                oracle.add_validator(auth_address, stake, commission, secret);

            // add validator to staking contract
            auto const staking_res = contract.precompile_add_validator(
                input, {} /* msg sender ignored */, msg_value);
            user_txn_success = !oracle_res.has_error();
            if (oracle_res.has_error()) {
                MONAD_ASSERT(
                    staking_res.has_error() &&
                    staking_res.error() == oracle_res.error());
            }
            else {
                MONAD_ASSERT(!staking_res.has_error());
            }

        } break;
        default:
            break;
        }
        if (user_txn_success) {
            state.pop_accept();
        }
        else {
            state.pop_reject();
        }
        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
        bytes32_t const block_id =
            (header.number == 0) ? NULL_HASH_BLAKE3 : bytes32_t{header.number};
        bs.commit(block_id, header, {}, {}, {}, {}, {}, {});
        tdb.finalize(header.number, block_id);
        parent_block_id = block_id;
        ++header.number;
    }

    quill::flush();

    return 0;
}
