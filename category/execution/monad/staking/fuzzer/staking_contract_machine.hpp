#include <category/execution/monad/staking/fuzzer/staking_contract_model.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>

#include <random>

namespace monad::staking::test
{
    class StakingContractMachine
    {
        using ValIdSet =
            vm::fuzzing::UniformSamplingSet<uint64_t>;

        using DelegatorSet = vm::fuzzing::UniformSamplingSet<
            std::pair<uint64_t, Address>, TupleHash<uint64_t, Address>>;

        using WithdrawalRequestSet = vm::fuzzing::UniformSamplingSet<
            std::tuple<uint64_t, Address, uint8_t>,
            TupleHash<uint64_t, Address, uint8_t>>;

        using AvailableWithdrawalIdsMap =
            std::unordered_map<
                std::tuple<uint64_t, uint256_t>,
                std::vector<u8_be>,
                TupleHash<uint64_t, uint256_t>>;

        StakingContractModel model_;
        std::mt19937_64 engine_;
        bool enable_pubkey_assertions_{false}; // TODO
        bool enable_trace_{false}; // TODO

        std::vector<Address> all_addresses_;
        DelegatorSet all_delegators_;
        std::vector<std::pair<u64_be, Address>> validator_auth_addresses_;
        std::unordered_map<uint64_t, Address> val_id_to_signer_;
        std::vector<u64_be> all_val_ids_;
        ValIdSet delegable_val_ids_;
        AvailableWithdrawalIdsMap available_withdrawal_ids_;
        WithdrawalRequestSet all_withdrawal_requests_;

        static constexpr uint256_t MIN_DELEGATE_STAKE = DUST_THRESHOLD;

        static constexpr uint256_t MAX_STAKE = UNIT_BIAS;

        static constexpr uint256_t MAX_DELEGABLE_STAKE =
            MAX_STAKE - MIN_DELEGATE_STAKE;

        static_assert(MAX_STAKE >= MIN_VALIDATE_STAKE);
        static_assert(MIN_VALIDATE_STAKE >= DUST_THRESHOLD);

    public:
        enum class Transition
        {
            syscall_on_epoch_change,
            syscall_snapshot,
            syscall_reward,
            precompile_add_validator,
            precompile_delegate,
            precompile_undelegate,
            precompile_compound,
            precompile_withdraw,
            precompile_claim_rewards,
            precompile_change_commission,
            precompile_external_reward,
            precompile_get_delegator,
            TRANSITION_COUNT
        };

        struct AssertState
        {
            std::unordered_set<uint64_t> valset_execution;
            std::unordered_set<uint64_t> valset_consensus;
            std::unordered_set<uint64_t> valset_snapshot;
        };

        using seed_t = std::mt19937_64::result_type;

        static_assert(std::numeric_limits<seed_t>::min() == 0);
        static_assert(
            std::numeric_limits<seed_t>::max() ==
            std::numeric_limits<uint64_t>::max());

        StakingContractMachine(seed_t);

        void assert_all_invariants();

        void assert_valset_invariants(AssertState const &);
        void assert_val_execution_invariants(AssertState const &);
        void assert_delegator_invariants(AssertState const &);
        void assert_accumulated_rewards_invariants(AssertState const &);
        void assert_linked_list_invariants(AssertState const &);
        void assert_solvency_invariants(AssertState const &);

        void for_all_val_ids(std::function<void(u64_be)>);
        void for_all_addresses(std::function<void(Address const &)>);
        void for_all_val_ids_and_addresses(
            std::function<void(u64_be, Address const &)>);

        bool transition(Transition);

        void skip_epochs(uint64_t);

        seed_t gen();

        Transition gen_transition();

        Address gen_new_address();

        Address gen_old_address();

        Address gen_new_or_old_address();

        uint256_t gen_uint256();

        uint256_t gen_bound_biased_uint256(
            uint256_t lower_bound, uint256_t upper_bound);

        std::pair<u64_be, Address> gen_validator_auth_address();

        Address gen_delegator_to_val_id(u64_be);

        std::optional<u64_be> gen_active_consensus_val_id();

        u64_be gen_delegable_val_id();

        u64_be gen_potential_val_id();

        std::pair<u64_be, Address> gen_delegator();

        void syscall_on_epoch_change();

        void syscall_snapshot();

        void syscall_reward();

        Address get_add_validator_message_auth_address(byte_string const &);

        std::tuple<
            Address,
            byte_string,
            byte_string,
            byte_string,
            Address,
            evmc_uint256be>
        gen_precompile_add_validator_input(
            uint256_t const &min_stake, uint256_t const &max_stake);

        u64_be model_precompile_add_validator(
            Address const &,
            byte_string const &,
            byte_string const &,
            byte_string const &,
            Address const &,
            evmc_uint256be const &);

        void precompile_add_validator();

        std::tuple<u64_be, Address, evmc_uint256be>
        gen_precompile_delegate_input();

        void model_precompile_delegate(
            u64_be, Address const &, evmc_uint256be const &);

        void precompile_delegate();

        std::optional<std::tuple<
            u64_be, u256_be, u8_be, Address, evmc_uint256be>>
        gen_precompile_undelegate_input(uint256_t const &min_undelegate);

        void model_precompile_undelegate(
            u64_be, u256_be, u8_be, Address const &, evmc_uint256be const &);

        void precompile_undelegate();

        std::optional<std::tuple<u64_be, Address, evmc_uint256be>>
        gen_precompile_compound_input();

        void model_precompile_compound(
            u64_be, Address const &, evmc_uint256be const &);

        [[nodiscard]]
        bool precompile_compound();

        std::optional<std::tuple<u64_be, u8_be, Address, evmc_uint256be>>
        gen_precompile_withdraw_input();

        void model_precompile_withdraw(
            u64_be, u8_be, Address const &, evmc_uint256be const &);

        [[nodiscard]]
        bool precompile_withdraw();

        std::tuple<u64_be, Address, evmc_uint256be>
        gen_precompile_claim_rewards_input();

        void model_precompile_claim_rewards(
            u64_be, Address const &, evmc_uint256be const &);

        void precompile_claim_rewards();

        std::tuple<u64_be, u256_be, Address, evmc_uint256be>
        gen_precompile_change_commission_input();

        void model_precompile_change_commission(
            u64_be, u256_be const &, Address const &, evmc_uint256be const &);

        void precompile_change_commission();

        std::optional<std::tuple<u64_be, Address, evmc_uint256be>>
        gen_precompile_external_reward_input();

        void model_precompile_external_reward(
            u64_be, Address const &, evmc_uint256be const &);

        bool precompile_external_reward();

        std::tuple<u64_be, Address, Address, evmc_uint256be>
        gen_precompile_get_delegator_input();

        void model_precompile_get_delegator(
            u64_be, Address const &, Address const &, evmc_uint256be const &);

        void precompile_get_delegator();
    };
}
