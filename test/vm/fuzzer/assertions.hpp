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

#include "account.hpp"
#include "state.hpp"

#include <evmc/evmc.hpp>

namespace monad::vm::fuzzing
{
    void assert_equal(
        evmone::state::StorageValue const &a,
        evmone::state::StorageValue const &b);

    void assert_equal(
        evmone::state::Account const &a, evmone::state::Account const &b);

    void
    assert_equal(evmc_revision const rev, evmone::state::State const &a, evmone::state::State const &b);

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool strict_out_of_gas);
}
