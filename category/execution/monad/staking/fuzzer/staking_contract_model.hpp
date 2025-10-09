#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>

namespace monad::staking::test
{
    template <typename T>
    using RefConstHash =
        std::hash<std::remove_const_t<std::remove_reference_t<T>>>;

    template <typename... T>
    struct TupleHash
    {
        std::size_t operator()(const std::tuple<T...>& tup) const noexcept
        {
            return std::apply([](auto const&... x) {
                return (RefConstHash<decltype(x)>{}(x) ^ ...);
            }, tup);
        }
    };
}

namespace std
{
    template <>
    struct hash<monad::uint256_t>
    {
        template <typename... T>
        std::size_t operator()(const monad::uint256_t& x) const noexcept
        {
            return monad::staking::test::RefConstHash<decltype(x[0])>{}(
                x[0] ^ x[1] ^ x[2] ^ x[3]);
        }
    };
}

namespace monad::staking::test
{
    class StakingContractModel
    {
        vm::VM vm_;
        OnDiskMachine mpt_machine_;
        mpt::Db mpt_db_{mpt_machine_};
        TrieDb trie_db_{mpt_db_};
        BlockState block_state_{trie_db_, vm_};
        State state_{block_state_, Incarnation{0, 0}};
        NoopCallTracer call_tracer_{};
        StakingContract contract_{state_, call_tracer_};

        // An upper bound on reward rounding errors:
        uint256_t error_bound_{};

        using UnitBiasRewardsMap = std::unordered_map<
            std::tuple<uint64_t, uint256_t>,
            uint256_t,
            TupleHash<uint64_t, uint256_t>>;

        // unit_bias_rewards[{v, a}] is the sum of rewards distributed to
        // delegator(v, a), but not yet claimed/compounded.
        UnitBiasRewardsMap unit_bias_rewards_;

        using ActiveConsensusStakeMap =
            std::unordered_map<uint64_t, uint256_t>;

        // The stake of the active consensus validators:
        ActiveConsensusStakeMap active_consensus_stake_;

        using ActiveConsensusCommissionMap =
            ActiveConsensusStakeMap;

        // The stake of the active consensus validators:
        ActiveConsensusCommissionMap active_consensus_commission_;

        using DelegatorStakeMap = std::unordered_map<
            std::tuple<uint64_t, uint256_t>,
            std::map<uint64_t, uint256_t, std::greater<uint64_t>>,
            TupleHash<uint64_t, uint256_t>>;

        // delegator_stake[{v, a, e}] is the stake of delegator(v, a)
        // in epoch e:
        DelegatorStakeMap delegator_stake_;

        using WithdrawalStakeMap = std::unordered_map<
            std::tuple<uint64_t, uint256_t, uint64_t>,
            uint256_t,
            TupleHash<uint64_t, uint256_t, uint64_t>>;

        // withdrawal_stake[{v, a, e}] is the stake of delegator(v, a)
        // in epoch e which has been undelegated, but the stake is eligible
        // for rewards.
        WithdrawalStakeMap withdrawal_stake_;

    public:
        StakingContractModel();

        uint256_t delegator_stake(u64_be, Address const &, u64_be);

        uint256_t withdrawal_stake(u64_be, Address const &, u64_be);

        uint256_t active_consensus_commission(u64_be);

        uint256_t active_consensus_stake(u64_be);

        uint256_t error_bound();

        bool in_epoch_delay_period();

        uint64_t last_val_id();

        uint64_t epoch();

        ValExecution val_execution(u64_be);

        Delegator delegator(u64_be, Address const &);

        StorageVariable<StakingContract::WithdrawalRequest>
        withdrawal_request(u64_be, Address const &, u8_be);

        StorageArray<u64_be> valset_execution();

        StorageArray<u64_be> valset_snapshot();

        StorageArray<u64_be> valset_consensus();

        ConsensusView consensus_view(u64_be);

        ConsensusView snapshot_view(u64_be);

        StorageVariable<u256_be> val_bitset_bucket(u64_be);

        std::vector<Address> get_delegators_for_validator(u64_be);

        static uint256_t calculate_rewards(
            uint256_t const &, uint256_t const &, uint256_t const &);

        uint256_t withdrawal_reward(u64_be, Address const &, u8_be);

        uint256_t unaccumulated_rewards(u64_be, evmc_address const &);

        uint256_t pending_rewards(u64_be, evmc_address const &);

        Result<void> syscall_on_epoch_change(u64_be);
        Result<void> syscall_snapshot();
        Result<void> syscall_reward(Address const &, u256_be const &);

        Result<u64_be> precompile_add_validator(
            byte_string_view message,
            byte_string_view secp_signature,
            byte_string_view bls_signature,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_delegate(
            u64_be val_id,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_undelegate(
            u64_be val_id,
            u256_be const &stake,
            u8_be withdrawal_id,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_compound(
            u64_be val_id,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_withdraw(
            u64_be val_id,
            u8_be withdrawal_id,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_claim_rewards(
            u64_be val_id,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_change_commission(
            u64_be val_id,
            u256_be const &new_commission,
            evmc_address const &sender,
            evmc_uint256be const &value);

        Result<void> precompile_external_reward(
            u64_be val_id,
            evmc_address const &sender,
            evmc_uint256be const &value);

        // Result type is not accurate. Just interested in the side
        // effects of this function on the state:
        Result<void> precompile_get_delegator(
            u64_be val_id,
            Address const &addr,
            evmc_address const &sender,
            evmc_uint256be const &value);

    private:
        uint256_t get_delegator_stake(
            uint64_t, uint256_t const &, uint64_t);
        uint256_t get_withdrawal_stake(
            uint64_t, uint256_t const &, uint64_t);
        void add_delegator_stake(
            uint64_t, uint256_t const &, uint64_t, uint256_t const &);
        void add_withdrawal_stake(
            uint64_t, uint256_t const &, uint64_t, uint256_t const &);

        void distribute_reward(u64_be, u256_be const &);

        void pre_call(evmc_uint256be const &value);

        template <typename T>
        void post_call(Result<T> const &);

        Result<byte_string> dispatch(
            byte_string const & input,
            evmc_address const &sender,
            evmc_uint256be const &value);
    };
}
