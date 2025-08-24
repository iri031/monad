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

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/vm/runtime/types.hpp>

#include <intx/intx.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <utility>

static_assert(sizeof(evmc::HostInterface) == 8);
static_assert(alignof(evmc::HostInterface) == 8);

static_assert(sizeof(evmc::Host) == 8);
static_assert(alignof(evmc::Host) == 8);

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;

class EvmcHostBase : public evmc::Host
{
    evmc_tx_context const &tx_context_;
    BlockHashBuffer const &block_hash_buffer_;

protected:
    State &state_;
    CallTracerBase &call_tracer_;
    size_t const max_code_size_;
    size_t const max_initcode_size_;
    bool const create_inside_delegated_;

public:
    EvmcHostBase(
        CallTracerBase &, evmc_tx_context const &, BlockHashBuffer const &,
        State &, size_t max_code_size, size_t max_initcode_size,
        bool create_inside_delegated) noexcept;

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

static_assert(sizeof(EvmcHostBase) == 64);
static_assert(alignof(EvmcHostBase) == 8);

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
            if (!create_inside_delegated_ && (msg.flags & EVMC_DELEGATED)) {
                return evmc::Result{EVMC_UNDEFINED_INSTRUCTION, msg.gas};
            }

            auto result =
                ::monad::create<rev>(this, state_, msg, max_code_size_);

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
            return ::monad::call(this, state_, msg);
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

    monad::vm::runtime::ChainParams get_chain_params() const noexcept
    {
        return {
            .max_initcode_size = max_initcode_size_,
        };
    }

    CallTracerBase &get_call_tracer() noexcept
    {
        return call_tracer_;
    }
};

static_assert(sizeof(EvmcHost<EVMC_LATEST_STABLE_REVISION>) == 64);
static_assert(alignof(EvmcHost<EVMC_LATEST_STABLE_REVISION>) == 8);

MONAD_NAMESPACE_END
