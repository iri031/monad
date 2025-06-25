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
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>

#include <cstdint>
#include <memory>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

struct NodeCursor
{
    std::unique_ptr<StateMachine> machine{nullptr};
    Node *node{nullptr};
    unsigned prefix_index{0};

    constexpr NodeCursor() {}

    constexpr NodeCursor(
        std::unique_ptr<StateMachine> machine_, Node &node_,
        unsigned const prefix_index_ = 0)
        : machine{std::move(machine_)}
        , node{&node_}
        , prefix_index{prefix_index_}
    {
        MONAD_ASSERT(machine != nullptr);
        MONAD_ASSERT(node != nullptr);
    }

    NodeCursor(NodeCursor const &o)
        : machine{o.machine ? o.machine->clone() : nullptr}
        , node{o.node}
        , prefix_index{o.prefix_index}
    {
    }

    NodeCursor &operator=(NodeCursor const &o)
    {
        if (this != &o) {
            this->~NodeCursor();
            new (this) NodeCursor(o);
        }
        return *this;
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }
};

static_assert(sizeof(NodeCursor) == 24);
static_assert(alignof(NodeCursor) == 8);
static_assert(std::is_copy_constructible_v<NodeCursor> == true);

struct OwningNodeCursor
{
    std::unique_ptr<StateMachine> machine{nullptr};
    std::shared_ptr<Node> node{nullptr};
    unsigned prefix_index{0};

    constexpr OwningNodeCursor() {}

    OwningNodeCursor(
        std::unique_ptr<StateMachine> machine_, std::shared_ptr<Node> node_,
        unsigned prefix_index_ = 0)
        : machine{std::move(machine_)}
        , node{node_}
        , prefix_index{prefix_index_}
    {
        MONAD_ASSERT(machine != nullptr);
        MONAD_ASSERT(node != nullptr);
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }

    OwningNodeCursor(OwningNodeCursor const &o)
        : machine{o.machine ? o.machine->clone() : nullptr}
        , node{o.node}
        , prefix_index{o.prefix_index}
    {
    }

    OwningNodeCursor &operator=(OwningNodeCursor const &o)
    {
        if (this != &o) {
            this->~OwningNodeCursor();
            new (this) OwningNodeCursor(o);
        }
        return *this;
    }

    OwningNodeCursor(OwningNodeCursor &&) = default;
    OwningNodeCursor &operator=(OwningNodeCursor &&) = default;
};

static_assert(sizeof(OwningNodeCursor) == 32);
static_assert(alignof(OwningNodeCursor) == 8);
static_assert(std::is_copy_constructible_v<OwningNodeCursor> == true);

MONAD_MPT_NAMESPACE_END
