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

#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>

#include <format>
#include <type_traits>
#include <utility>

namespace detail
{
    template <monad_revision rev>
    using MonadRevisionConstant = std::integral_constant<monad_revision, rev>;

    template <std::size_t... Is>
    constexpr auto make_monad_revision_types(std::index_sequence<Is...>)
    {
        return ::testing::Types<
            MonadRevisionConstant<static_cast<monad_revision>(Is)>...>{};
    }

    using MonadRevisionTypes = decltype(make_monad_revision_types(
        std::make_index_sequence<MONAD_COUNT>{}));

    struct MonadRevisionTestNameGenerator
    {
        template <typename T>
        static std::string GetName(int)
        {
            return std::string(monad_revision_to_string(T::value));
        }
    };
}

template <typename MonadRevisionT>
struct MonadRevisionTest : public ::testing::Test
{
    static constexpr monad_revision REV = MonadRevisionT::value;
    using Trait = monad::MonadTraits<REV>;
};

TYPED_TEST_SUITE(
    MonadRevisionTest, ::detail::MonadRevisionTypes,
    ::detail::MonadRevisionTestNameGenerator);
