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
#include <ranges>
#include <set>
#include <unordered_map>

#include <blst.h>
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

    struct Delegator
    {
        uint256_t stake;
        uint256_t rewards;
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
    using ConsensusValidatorSet = std::list<ConsensusViewOracle>;

    using ExecutionValidatorHandle = ExecutionValidatorSet::iterator;
    using ConsensusValidatorHandle = ConsensusValidatorSet::iterator;

    // execution view
    ExecutionValidatorSet execution_validator_set{};
    std::unordered_map<uint64_t, ExecutionValidatorHandle>
        execution_validator_map;
    uint64_t last_validator_id = 0;
    std::unordered_set<bytes32_t> used_secrets;
    bool in_epoch_delay_period = false;

    // consensus view
    ConsensusValidatorSet consensus_validator_set;
    ConsensusValidatorSet snapshot_validator_set;

    std::unordered_map<uint64_t, ConsensusValidatorHandle>
        consensus_validator_map;
    std::unordered_map<uint64_t, ConsensusValidatorHandle>
        snapshot_validator_map;

    ValidatorOracle pop_validator(uint64_t const val_id)
    {
        auto it = execution_validator_map.find(val_id);
        MONAD_ASSERT(it != execution_validator_map.end());

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
        execution_validator_map.try_emplace(validator.id, it);
    }

public:
    ////////////////////
    // Fuzzer actions //
    ////////////////////
    bool in_epoch_delay() const
    {
        return in_epoch_delay_period;
    }

    bool add_validator(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission, bytes32_t const &secret)
    {
        auto [_, inserted] = used_secrets.emplace(secret);
        if (inserted) {
            uint64_t validator_id = ++last_validator_id;

            insert_validator(ValidatorOracle{
                .id = validator_id,
                .auth_address = auth_address,
                .stake = 0, /* updated in delegate */
                .commission = commission,
                .rewards_per_token = 0,
                .flags = ValidatorFlagsStakeTooLow, /* updated in delegate if
                                                    appropriate */
            });
            delegate(validator_id, auth_address, stake);
        }

        return !inserted; // staking contract bans reused keys
    }

    void delegate(
        uint64_t const val_id, Address const &delegator, uint256_t const &stake)
    {
        ValidatorOracle validator = pop_validator(val_id);
        validator.stake += stake;

        if (validator.stake >= ACTIVE_VALIDATOR_STAKE) {
            validator.flags = validator.flags & ~ValidatorFlagsStakeTooLow;
        }

        if (validator.auth_address == delegator &&
            validator.stake >= MIN_VALIDATE_STAKE) {
            validator.flags = validator.flags & ~ValidatorFlagWithdrawn;
        }
        insert_validator(std::move(validator));
    }

    void snapshot()
    {
        snapshot_validator_set = std::move(consensus_validator_set);
        snapshot_validator_map = std::move(consensus_validator_map);

        // take top N validators. valset is a max heap, so just iterate that.
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

    void epoch_change() {}

    //////////////////////
    // Verify Functions //
    //////////////////////

    void verify_after_snapshot(StakingContract &contract)
    {
        // consensus set
        MONAD_ASSERT(
            contract.vars.valset_consensus.length() ==
            consensus_validator_set.size());
        for (auto const &&[i, cv] :
             std::ranges::views::enumerate(consensus_validator_set)) {
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
             std::ranges::views::enumerate(snapshot_validator_set)) {
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
        // DELEGATE,
        // UNDELEGATE,
        kMaxValue, /* For the fuzzed data provider */
    };

    while (provider.remaining_bytes() > 0) {
        if (header.number > 0) {
            tdb.set_block_and_prefix(header.number - 1);
        }
        BlockState bs{tdb, vm};
        {
            State state{bs, Incarnation{header.number, 0}};
            StakingContract contract(state);
            state.add_to_balance(
                STAKING_CA, 0); // creates staking account in state

            // Maybe perform a state change?
            if (provider.ConsumeProbability<float>() < 0.2) {
                oracle.snapshot();
                MONAD_ASSERT(!contract.syscall_snapshot({}).has_error());
                oracle.verify_after_snapshot(contract);
            }
            MONAD_ASSERT(bs.can_merge(state));
            bs.merge(state);
        }

        // TODO: Reward

        // Fuzz a user transaction
        State state{bs, Incarnation{header.number, 0}};
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
                continue;
            }

            // auth address is how we check validator existence. they won't get
            // the zero address.
            if (auth_address == Address{}) {
                continue;
            }

            uint256_t const stake = consume_u256_in_range(
                provider, MIN_VALIDATE_STAKE, ACTIVE_VALIDATOR_STAKE);
            uint256_t const commission =
                consume_u256_in_range(provider, 0, MON);

            // add validator to oracle
            bool const dup =
                oracle.add_validator(auth_address, stake, commission, secret);

            // add validator to staking contract
            auto [input, _] = craft_add_validator_input(
                auth_address, stake, commission, secret);
            state.add_to_balance(STAKING_CA, stake);
            auto const msg_value = intx::be::store<evmc_uint256be>(stake);
            auto const res = contract.precompile_add_validator(
                input, {} /* msg sender ignored */, msg_value);
            user_txn_success = !res.has_error();
            if (dup) {
                MONAD_ASSERT(
                    res.has_error() &&
                    res.error() == StakingError::ValidatorExists);
            }
            else {
                MONAD_ASSERT(!res.has_error());
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
        bs.commit(bytes32_t{header.number + 1}, header, {}, {}, {}, {}, {}, {});
        tdb.finalize(header.number, bytes32_t{header.number + 1});
        ++header.number;
    }

    quill::flush();

    return 0;
}
