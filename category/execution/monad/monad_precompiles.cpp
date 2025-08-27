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

#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/monad_precompiles.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>

MONAD_NAMESPACE_BEGIN

std::optional<evmc::Result> check_call_monad_precompile(
    monad_revision const rev, State &state, evmc_message const &msg)
{
    if (MONAD_UNLIKELY(rev < MONAD_THREE)) {
        return std::nullopt;
    }

    if (msg.code_address != staking::STAKING_CA) {
        return std::nullopt;
    }

    if (MONAD_UNLIKELY(msg.kind != EVMC_CALL) || (msg.flags != 0)) {
        return evmc::Result{evmc_status_code::EVMC_REJECTED};
    }

    byte_string_view input{msg.input_data, msg.input_size};
    auto const [method, cost] =
        staking::StakingContract::precompile_dispatch(input);
    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    staking::StakingContract contract(state);
    auto const res = (contract.*method)(input, msg.sender, msg.value);
    if (MONAD_LIKELY(res.has_value())) {
        int64_t const gas_left = msg.gas - static_cast<int64_t>(cost);
        int64_t const gas_refund = 0;
        return evmc::Result(
            EVMC_SUCCESS,
            gas_left,
            gas_refund,
            res.value().data(),
            res.value().size());
    }
    return evmc::Result(
        EVMC_REVERT,
        0 /* gas left */,
        0 /* gas refund */,
        reinterpret_cast<uint8_t const *>(res.error().message().data()),
        res.error().message().size());
}

MONAD_NAMESPACE_END
