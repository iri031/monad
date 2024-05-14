#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/trace.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

void merge(
    std::map<Address, std::map<bytes32_t, std::vector<AccessOp>>> &a,
    std::map<Address, std::map<bytes32_t, std::vector<AccessOp>>> const &b)
{
    for (auto const &b_outer_pair : b) {
        Address const &b_address = b_outer_pair.first;
        auto const &b_inner_map = b_outer_pair.second;

        if (a.find(b_address) == a.end()) {
            // If key does not exist in `a`, insert the whole sub-map from `b`
            a[b_address] = b_inner_map;
        }
        else {
            // If key exists, merge the inner maps
            auto &a_inner_map = a[b_address];
            for (auto const &b_inner_pair : b_inner_map) {
                bytes32_t const &b_key = b_inner_pair.first;
                std::vector<AccessOp> const &b_vector = b_inner_pair.second;

                if (a_inner_map.find(b_key) == a_inner_map.end()) {
                    // If inner key does not exist, insert the whole vector
                    a_inner_map[b_key] = b_vector;
                }
                else {
                    // If inner key exists, append the vector
                    auto &a_vector = a_inner_map[b_key];
                    a_vector.insert(
                        a_vector.end(), b_vector.begin(), b_vector.end());
                }
            }
        }
    }
}

// YP Sec 6.2 "irrevocable_change"
template <evmc_revision rev>
constexpr void irrevocable_change(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas)
{
    if (tx.to) { // EVM will increment if new contract
        auto const nonce = state.get_nonce(sender);
        state.set_nonce(sender, nonce + 1);
    }

    auto const upfront_cost =
        tx.gas_limit * gas_price<rev>(tx, base_fee_per_gas);
    state.subtract_from_balance(sender, upfront_cost);
}

// YP Eqn 72
template <evmc_revision rev>
constexpr uint64_t g_star(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    // EIP-3529
    constexpr auto max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
    auto const refund_allowance =
        (tx.gas_limit - gas_remaining) / max_refund_quotient;

    return gas_remaining + std::min(refund_allowance, refund);
}

template <evmc_revision rev>
constexpr auto refund_gas(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas, uint64_t const gas_leftover,
    uint64_t const refund)
{
    // refund and priority, Eqn. 73-76
    auto const gas_remaining = g_star<rev>(tx, gas_leftover, refund);
    auto const gas_cost = gas_price<rev>(tx, base_fee_per_gas);

    state.add_to_balance(sender, gas_cost * gas_remaining);

    return gas_remaining;
}

template <evmc_revision rev>
constexpr evmc_message to_message(Transaction const &tx, Address const &sender)
{
    auto const to_address = [&tx] {
        if (tx.to) {
            return std::pair{EVMC_CALL, *tx.to};
        }
        return std::pair{EVMC_CREATE, Address{}};
    }();

    evmc_message msg{
        .kind = to_address.first,
        .flags = 0,
        .depth = 0,
        .gas = static_cast<int64_t>(tx.gas_limit - intrinsic_gas<rev>(tx)),
        .recipient = to_address.second,
        .sender = sender,
        .input_data = tx.data.data(),
        .input_size = tx.data.size(),
        .value = {},
        .create2_salt = {},
        .code_address = to_address.second,
    };
    intx::be::store(msg.value.bytes, tx.value);
    return msg;
}

template <evmc_revision rev>
evmc::Result execute_impl_no_validation(
    State &state, EvmcHost<rev> &host, Transaction const &tx,
    Address const &sender, uint256_t const &base_fee_per_gas,
    Address const &beneficiary)
{
    irrevocable_change<rev>(state, tx, sender, base_fee_per_gas);

    // EIP-3651
    if constexpr (rev >= EVMC_SHANGHAI) {
        host.access_account(beneficiary);
    }

    state.access_account(sender);
    for (auto const &ae : tx.access_list) {
        state.access_account(ae.a);
        for (auto const &keys : ae.keys) {
            state.access_storage(ae.a, keys);
        }
    }
    if (MONAD_LIKELY(tx.to)) {
        state.access_account(*tx.to);
    }

    auto const msg = to_message<rev>(tx, sender);
    return host.call(msg);
}

EXPLICIT_EVMC_REVISION(execute_impl_no_validation);

template <evmc_revision rev>
Receipt execute_final(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas, evmc::Result const &result,
    Address const &beneficiary)
{
    MONAD_ASSERT(result.gas_left >= 0);
    MONAD_ASSERT(result.gas_refund >= 0);
    MONAD_ASSERT(tx.gas_limit >= static_cast<uint64_t>(result.gas_left));
    auto const gas_remaining = refund_gas<rev>(
        state,
        tx,
        sender,
        base_fee_per_gas,
        static_cast<uint64_t>(result.gas_left),
        static_cast<uint64_t>(result.gas_refund));
    auto const gas_used = tx.gas_limit - gas_remaining;
    auto const reward =
        calculate_txn_award<rev>(tx, base_fee_per_gas, gas_used);
    state.add_to_balance(beneficiary, reward);

    // finalize state, Eqn. 77-79
    state.destruct_suicides();
    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    Receipt receipt{
        .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
        .gas_used = gas_used,
        .type = tx.type};
    for (auto const &log : state.logs()) {
        receipt.add_log(std::move(log));
    }

    return receipt;
}

template <evmc_revision rev>
Result<evmc::Result> execute_impl2(
    Transaction const &tx, Address const &sender, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, State &state)
{
    auto const sender_account = state.recent_account(sender);
    BOOST_OUTCOME_TRY(validate_transaction(tx, sender_account));

    auto const tx_context = get_tx_context<rev>(tx, sender, hdr);
    EvmcHost<rev> host{tx_context, block_hash_buffer, state};

    return execute_impl_no_validation<rev>(
        state,
        host,
        tx,
        sender,
        hdr.base_fee_per_gas.value_or(0),
        hdr.beneficiary);
}

template <evmc_revision rev>
Result<Receipt> execute_impl(
    [[maybe_unused]] uint64_t const i, Transaction const &tx,
    Address const &sender, BlockHeader const &hdr,
    BlockHashBuffer const &block_hash_buffer, BlockState &block_state,
    boost::fibers::promise<void> &prev,
    std::map<Address, std::map<bytes32_t, std::vector<AccessOp>>>
        &storage_accesses)
{
    BOOST_OUTCOME_TRY(
        static_validate_transaction<rev>(tx, hdr.base_fee_per_gas));

    {
        TRACE_TXN_EVENT(StartExecution);

        State state{block_state, Incarnation{hdr.number, i + 1}};

        auto result =
            execute_impl2<rev>(tx, sender, hdr, block_hash_buffer, state);

        {
            TRACE_TXN_EVENT(StartStall);
            prev.get_future().wait();
        }

        if (block_state.can_merge(state)) {
            if (result.has_error()) {
                return std::move(result.error());
            }
            auto const receipt = execute_final<rev>(
                state,
                tx,
                sender,
                hdr.base_fee_per_gas.value_or(0),
                result.value(),
                hdr.beneficiary);
            block_state.merge(state);

            // merge1
            merge(storage_accesses, state.storage_accesses_);
            return receipt;
        }
    }
    {
        TRACE_TXN_EVENT(StartRetry);

        State state{block_state, Incarnation{hdr.number, i + 1}};

        auto result =
            execute_impl2<rev>(tx, sender, hdr, block_hash_buffer, state);

        MONAD_ASSERT(block_state.can_merge(state));
        if (result.has_error()) {
            return std::move(result.error());
        }
        auto const receipt = execute_final<rev>(
            state,
            tx,
            sender,
            hdr.base_fee_per_gas.value_or(0),
            result.value(),
            hdr.beneficiary);
        block_state.merge(state);

        merge(storage_accesses, state.storage_accesses_);
        return receipt;
    }
}

EXPLICIT_EVMC_REVISION(execute_impl);

template <evmc_revision rev>
Result<Receipt> execute(
    [[maybe_unused]] uint64_t const i, Transaction const &tx,
    BlockHeader const &hdr, BlockHashBuffer const &block_hash_buffer,
    BlockState &block_state, boost::fibers::promise<void> &prev,
    std::map<Address, std::map<bytes32_t, std::vector<AccessOp>>>
        &storage_accesses)
{
    TRACE_TXN_EVENT(StartTxn);

    auto const sender = recover_sender(tx);

    if (MONAD_UNLIKELY(!sender.has_value())) {
        return TransactionError::MissingSender;
    }

    return execute_impl<rev>(
        i,
        tx,
        sender.value(),
        hdr,
        block_hash_buffer,
        block_state,
        prev,
        storage_accesses);
}

EXPLICIT_EVMC_REVISION(execute);

MONAD_NAMESPACE_END
