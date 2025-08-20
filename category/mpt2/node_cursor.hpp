#pragma once
#include <category/mpt2/config.hpp>
#include <category/mpt2/node.hpp>

#include <cstdint>

MONAD_MPT2_NAMESPACE_BEGIN

struct NodeCursor
{
    Node *node{nullptr};
    unsigned prefix_index{0};

    constexpr NodeCursor()
        : node{nullptr}
        , prefix_index{0}
    {
    }

    constexpr NodeCursor(Node &node_, unsigned prefix_index_ = 0)
        : node{&node_}
        , prefix_index{prefix_index_}
    {
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }
};

static_assert(sizeof(NodeCursor) == 16);
static_assert(alignof(NodeCursor) == 8);
static_assert(std::is_trivially_copyable_v<NodeCursor> == true);

// Contains copy of the node so is safe to access even if node's version is
// invalidated and node is overwritten on disk.
struct OwningNodeCursor
{
    Node::UniquePtr node;
    unsigned prefix_index{0};

    constexpr OwningNodeCursor() = default;

    constexpr OwningNodeCursor(Node::UniquePtr node, unsigned prefix_index = 0)
        : node{std::move(node)}
        , prefix_index{prefix_index}
    {
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }

    OwningNodeCursor clone() const
    {
        return OwningNodeCursor(copy_node(*node), prefix_index);
    }
};

MONAD_MPT2_NAMESPACE_END
