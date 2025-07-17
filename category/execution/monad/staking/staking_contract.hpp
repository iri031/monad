#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/staking/util/del_info.hpp>
#include <category/execution/monad/staking/util/val_consensus.hpp>
#include <category/execution/monad/staking/util/val_execution.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>
#include <string_view>

MONAD_NAMESPACE_BEGIN

class State;

class StakingContract
{
    State &state_;
    Address const &ca_;

public:
    //////////////////////
    //  Revert Codes   //
    //////////////////////
    enum Status
    {
        SUCCESS = 0,
        INTERNAL_ERROR,
        METHOD_NOT_SUPPORTED,
        INVALID_INPUT,
        VALIDATOR_EXISTS,
        UNKNOWN_VALIDATOR,
        UNKNOWN_DELEGATOR,
        WITHDRAWAL_ID_EXISTS,
        UNKNOWN_WITHDRAWAL_ID,
        WITHDRAWAL_NOT_READY,
        INSUFFICIENT_STAKE,
        INVALID_SECP_PUBKEY,
        INVALID_BLS_PUBKEY,
        INVALID_SECP_SIGNATURE,
        INVALID_BLS_SIGNATURE,
        SECP_SIGNATURE_VERIFICATION_FAILED,
        BLS_SIGNATURE_VERIFICATION_FAILED,
        BLOCK_AUTHOR_NOT_IN_SET,
        STATUS_CODES_LENGTH,
    };

    struct Output
    {
        Status status;
        byte_string data;

        Output(Status const status_)
            : status{status_}
        {
        }

        Output(byte_string data_)
            : status{SUCCESS}
            , data{std::move(data_)}
        {
        }
    };

    static constexpr std::string_view error_message(Status const res)
    {
        static constexpr std::array<std::string_view, STATUS_CODES_LENGTH>
            REVERT_MSG{
                "Success",
                "Internal contract error",
                "Method not supported",
                "Input invalid",
                "Validator already exists",
                "Unknown validator",
                "Unknown delegator",
                "Withdrawal id exists",
                "Unknown withdrawal id",
                "Withdrawal not ready",
                "Insufficient stake to perform operation",
                "Invalid secp256k1 pubkey",
                "Invalid bls pubkey",
                "Invalid secp256k1 signature",
                "Secp256k1 signature verification failed",
                "Bls signature verification failed",
                "Invalid bls signature",
                "Block author not in set",
            };
        return REVERT_MSG[res];
    }

    StakingContract(State &, Address const &);

    struct WithdrawalRequest
    {
        u256_be amount;
        u256_be acc;
        u64_be epoch;
    };

    static_assert(sizeof(WithdrawalRequest) == 72);
    static_assert(alignof(WithdrawalRequest) == 1);

    struct Accumulator
    {
        u256_be value;
        u256_be refcount;
    };

    static_assert(sizeof(Accumulator) == 64);
    static_assert(alignof(Accumulator) == 1);

    class Variables
    {
        State &state_;
        Address const &ca_;

        // Single slot constants all under prefix 0x0
        static constexpr auto AddressEpoch{
            0x0000000000000000000000000000000000000000000000000000000000000001_bytes32};
        static constexpr auto AddressInBoundary{
            0x0000000000000000000000000000000000000000000000000000000000000002_bytes32};
        static constexpr auto AddressLastValId{
            0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
        static constexpr auto AddressValsetConsensusPointer{
            0x0000000000000000000000000000000000000000000000000000000000000005_bytes32};
        static constexpr auto AddressValInfoConsensusPointer{
            0x0000000000000000000000000000000000000000000000000000000000000006_bytes32};

        // Working valsets get prefixes 0x1, 0x2, 0x3
        static constexpr auto AddressValsetExecution{
            0x0100000000000000000000000000000000000000000000000000000000000000_bytes32};
        static constexpr auto AddressValsetConsensus1{
            0x0200000000000000000000000000000000000000000000000000000000000000_bytes32};
        static constexpr auto AddressValsetConsensus2{
            0x0300000000000000000000000000000000000000000000000000000000000000_bytes32};

        // Prefixes for mappings
        enum : uint8_t
        {
            PrefixConsensusValInfo1 = 0x04,
            PrefixConsensusValInfo2 = 0x05,
            PrefixValIdSecp = 0x06,
            PrefixValIdBls = 0x07,
            PrefixValBitset = 0x08,
            PrefixValExecution = 0x09,
            PrefixAccumulator = 0x0A,
            PrefixDelegator = 0x0B,
            PrefixWithdrawalRequest = 0x0C,
        };

    public:
        static std::string_view revert_message(Status);

        explicit Variables(State &state, Address const &ca)
            : state_{state}
            , ca_{ca}
        {
        }

        /////////////////////////
        //  Constant Addresses //
        /////////////////////////
        StorageVariable<bytes32_t> consensus_valset_pointer{
            state_, ca_, AddressValsetConsensusPointer};
        StorageVariable<uint8_t> consensus_valinfo_pointer{
            state_, ca_, AddressValInfoConsensusPointer};

    public:
        StorageVariable<u64_be> epoch{state_, ca_, AddressEpoch};
        StorageVariable<bool> in_boundary{state_, ca_, AddressInBoundary};
        StorageVariable<u64_be> last_val_id{state_, ca_, AddressLastValId};
        StorageArray<u64_be> valset_execution{
            state_, ca_, AddressValsetExecution};

        auto deref_consensus_valset() noexcept
        {
            return consensus_valset_pointer.load_checked().value_or(
                AddressValsetConsensus1);
        }

        auto deref_snapshot_valset() noexcept
        {
            return deref_consensus_valset() == AddressValsetConsensus1
                       ? AddressValsetConsensus2
                       : AddressValsetConsensus1;
        }

        auto deref_consensus_valinfo() noexcept
        {
            return consensus_valinfo_pointer.load_checked().value_or(
                PrefixConsensusValInfo1);
        }

        auto deref_snapshot_valinfo() noexcept
        {
            return deref_consensus_valinfo() == PrefixConsensusValInfo1
                       ? PrefixConsensusValInfo2
                       : PrefixConsensusValInfo1;
        }

        ////////////////
        //  Mappings  //
        ////////////////

        // mapping (address => uint64) val_id
        auto val_id(Address const &secp_eth_address) noexcept
        {
            struct
            {
                uint8_t mask;
                Address address;
                uint8_t slots[11];
            } key{
                .mask = PrefixValIdSecp,
                .address = secp_eth_address,
                .slots = {}};

            return StorageVariable<u64_be>(
                state_, ca_, std::bit_cast<bytes32_t>(key));
        }

        // mapping (address => uint64) val_id
        // This mapping only exists to ensure the same bls_key cannot be
        // assigned to multiple validator ids.
        auto val_id_bls(Address const &bls_eth_address) noexcept
        {
            struct
            {
                uint8_t mask;
                Address address;
                uint8_t slots[11];
            } key{
                .mask = PrefixValIdBls,
                .address = bls_eth_address,
                .slots = {}};

            return StorageVariable<u64_be>(
                state_, ca_, std::bit_cast<bytes32_t>(key));
        }

        // mapping(uint64 => mapping(uint64 => bytes32)) acc
        auto acc(u64_be const epoch, u64_be const val_id) noexcept
        {
            struct
            {
                uint8_t mask;
                u64_be epoch;
                u64_be val_id;
                uint8_t slots[15];
            } key{
                .mask = PrefixAccumulator,
                .epoch = epoch,
                .val_id = val_id,
                .slots = {}};

            return StorageVariable<Accumulator>(
                state_, ca_, std::bit_cast<bytes32_t>(key));
        }

        // mapping(uint64 => Validator) validator_info
        auto val_execution(u64_be const id) noexcept
        {
            struct
            {
                uint8_t mask;
                u64_be val_id;
                uint8_t slots[23];
            } key{.mask = PrefixValExecution, .val_id = id, .slots = {}};

            return ValExecution{state_, ca_, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => Validator) validator
        auto _val_consensus(u64_be const id) noexcept
        {
            struct
            {
                uint8_t mask;
                u64_be val_id;
                uint8_t slots[23];
            } key{.mask = deref_consensus_valinfo(), .val_id = id, .slots = {}};

            return ValConsensus{state_, ca_, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => Validator) validator
        auto _val_snapshot(u64_be const id) noexcept
        {
            struct
            {
                uint8_t mask;
                u64_be val_id;
                uint8_t slots[23];
            } key{.mask = deref_snapshot_valinfo(), .val_id = id, .slots = {}};

            return ValConsensus{state_, ca_, std::bit_cast<bytes32_t>(key)};
        }

        // mapping(uint64 => Validator) validator
        auto val_consensus(u64_be const id) noexcept
        {
            return in_boundary.load_checked().has_value() ? _val_snapshot(id)
                                                          : _val_consensus(id);
        }

        // mapping(bytes32_t* => Array[uint256])
        auto _valset_snapshot() noexcept
        {
            return StorageArray<u64_be>{state_, ca_, deref_snapshot_valset()};
        }

        // mapping(bytes32_t* => Array[uint256])
        auto _valset_consensus() noexcept
        {
            return StorageArray<u64_be>{state_, ca_, deref_consensus_valset()};
        }

        // A higher level API that abstracts away the boundary delay from the
        // staking contract.
        auto valset_consensus() noexcept
        {
            return in_boundary.load_checked().has_value() ? _valset_snapshot()
                                                          : _valset_consensus();
        }

        // mapping(uint64 => mapping(address => Delegator)) delegator_info
        auto delegator(u64_be const val_id, Address const &address) noexcept
        {
            struct
            {
                uint8_t mask;
                u64_be val_id;
                Address address;
                uint8_t slots[3];
            } key{
                .mask = PrefixDelegator,
                .val_id = val_id,
                .address = address,
                .slots = {}};

            return DelInfo{state_, ca_, std::bit_cast<bytes32_t>(key)};
        }

        // clang-format off
        // mapping(uint64 => mapping(address => mapping (uint8 => WithdrawalRequest)))
        // clang-format on
        auto withdrawal_request(
            u64_be const val_id, Address const &delegator,
            uint8_t const withdrawal_id) noexcept
        {
            struct
            {
                uint8_t mask;
                u64_be val_id;
                Address address;
                uint8_t withdrawal_id;
                uint8_t slots[2];
            } key{
                .mask = PrefixWithdrawalRequest,
                .val_id = val_id,
                .address = delegator,
                .withdrawal_id = withdrawal_id,
                .slots = {}};

            return StorageVariable<WithdrawalRequest>{
                state_, ca_, std::bit_cast<bytes32_t>(key)};
        }
    } vars;

private:
    /////////////
    // Events //
    /////////////

    // event ValidatorCreated(
    //     uint64  indexed valId,
    //     address indexed auth_delegator);
    void
    emit_validator_created_event(u64_be val_id, Address const &auth_delegator);

    // event ValidatorStatusChanged(
    //     uint64  indexed valId,
    //     address indexed auth_delegator,
    //     uint64          flags);
    void emit_validator_status_changed_event(u64_be val_id, u64_be flags);

    // event Delegate(
    //     uint64  indexed valId,
    //     address indexed delegator,
    //     uint256         amount,
    //     uint64          activationEpoch);
    void emit_delegation_event(
        u64_be val_id, Address const &delegator, u256_be const &amount,
        u64_be activation_epoch);

    // event Undelegate(
    //      uint64  indexed valId,
    //      address indexed delegator,
    //      uint8           withdrawal_id,
    //      uint256         amount,
    //      uint64          activationEpoch);
    void emit_undelegate_event(
        u64_be val_id, Address const &delegator, uint8_t withdrawal_id,
        u256_be amount, u64_be activation_epoch);

    // event ClaimRewards(
    // uint256 indexed valId,
    // address indexed delegatorAddress
    // uint256         amount);
    void emit_claim_rewards_event(
        u64_be val_id, Address const &delegator, u256_be const &amount);

    /////////////
    // Helpers //
    /////////////
    void mint_tokens(uint256_t const &);
    void send_tokens(Address const &, uint256_t const &);

    void inc_acc_refcount(u64_be epoch, u64_be const val_id);
    u256_be dec_acc_refcount(u64_be epoch, u64_be const val_id);

    uint64_t get_activation_epoch() const noexcept;
    bool is_epoch_active(uint64_t) const noexcept;
    void touch_delegator(u64_be, DelInfo &);
    void apply_compound(u64_be, DelInfo &);

    Output add_stake(u64_be, uint256_t const &, Address const &);

public:
    using PrecompileFunc = Output (StakingContract::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    /////////////////
    // Precompiles //
    /////////////////
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Output precompile_get_validator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_get_delegator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

    Output precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_add_validator(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_delegate(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_undelegate(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_compound(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_withdraw(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output precompile_claim_rewards(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

    ////////////////////
    //  System Calls  //
    ////////////////////
    Output syscall_on_epoch_change(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output syscall_reward(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
    Output syscall_snapshot(
        byte_string_view, evmc_address const &, evmc_uint256be const &);
};

MONAD_NAMESPACE_END
