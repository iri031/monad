#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>

#include <intx/intx.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <functional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;

class EvmcHostBase : public evmc::Host
{
    BlockHashBuffer const &block_hash_buffer_;

protected:
    evmc_tx_context const &tx_context_;
    State &state_;
    CallTracerBase &call_tracer_;
    std::function<evmc::Result(EvmcHostBase &, evmc_message const &)> call_;
    std::function<evmc::Result(EvmcHostBase &, evmc_message const &)> create_;
    uint64_t i_;
    Chain const &chain_;
    void *chain_context_;

public:
    EvmcHostBase(
        CallTracerBase &, evmc_tx_context const &, BlockHashBuffer const &,
        State &,
        std::function<evmc::Result(EvmcHostBase &, evmc_message const &)> call,
        std::function<evmc::Result(EvmcHostBase &, evmc_message const &)>
            create,
        uint64_t i, Chain const &, void *chain_context) noexcept;

    virtual ~EvmcHostBase() noexcept = default;

    virtual bytes32_t
    get_storage(Address const &, bytes32_t const &key) const noexcept override;

    virtual evmc_storage_status set_storage(
        Address const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;

    virtual evmc::uint256be
    get_balance(Address const &) const noexcept override;

    virtual size_t get_code_size(Address const &) const noexcept override;

    virtual bytes32_t get_code_hash(Address const &) const noexcept override;

    virtual size_t copy_code(
        Address const &, size_t offset, uint8_t *data,
        size_t size) const noexcept override;

    virtual evmc_tx_context get_tx_context() const noexcept override;

    virtual bytes32_t get_block_hash(int64_t) const noexcept override;

    virtual void emit_log(
        Address const &, uint8_t const *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) noexcept override;

    virtual evmc_access_status
    access_storage(Address const &, bytes32_t const &key) noexcept override;

    virtual bytes32_t get_transient_storage(
        Address const &, bytes32_t const &key) const noexcept override;

    virtual void set_transient_storage(
        Address const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;
};

template <evmc_revision rev>
struct EvmcHost final : public EvmcHostBase
{
    using EvmcHostBase::EvmcHostBase;

    virtual bool account_exists(Address const &address) const noexcept override
    {
        if constexpr (rev < EVMC_SPURIOUS_DRAGON) {
            return state_.account_exists(address);
        }
        return !state_.account_is_dead(address);
    }

    virtual bool selfdestruct(
        Address const &address, Address const &beneficiary) noexcept override
    {
        call_tracer_.on_self_destruct(address, beneficiary);
        return state_.selfdestruct<rev>(address, beneficiary);
    }

    virtual evmc::Result call(evmc_message const &msg) noexcept override
    {
        if (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2) {
            evmc::Result result = create_(*this, msg);

            // EIP-211
            if (result.status_code != EVMC_REVERT) {
                result = evmc::Result{
                    result.status_code,
                    result.gas_left,
                    result.gas_refund,
                    result.create_address};
            }
            return result;
        }
        else {
            return call_(*this, msg);
        }
    }

    virtual evmc_access_status
    access_account(Address const &address) noexcept override
    {
        if (is_precompile<rev>(address)) {
            return EVMC_ACCESS_WARM;
        }
        return state_.access_account(address);
    }
};

MONAD_NAMESPACE_END
