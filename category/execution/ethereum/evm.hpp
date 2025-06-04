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

#include <category/execution/ethereum/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct CallTracerBase;
struct Chain;
class EvmcHostBase;
class State;

template <evmc_revision rev>
class Create
{
    Chain const &chain_;
    State &state_;
    BlockHeader const &header_;
    CallTracerBase &call_tracer_;

public:
    Create(Chain const &, State &, BlockHeader const &, CallTracerBase &);

    evmc::Result operator()(EvmcHostBase &, evmc_message const &) noexcept;
    evmc::Result deploy_contract_code(Address const &, evmc::Result) noexcept;
};

template <evmc_revision rev>
class Call
{
    State &state_;
    CallTracerBase &call_tracer_;
    Chain const &chain_;
    uint64_t i_;
    Transaction const &tx_;
    void *chain_context_;

    std::optional<evmc::Result> pre_call(evmc_message const &);
    void post_call(evmc::Result const &);

public:
    Call(
        State &, CallTracerBase &, Chain const &, uint64_t, Transaction const &,
        void *);

    evmc::Result operator()(EvmcHostBase &, evmc_message const &) noexcept;
};

MONAD_NAMESPACE_END
