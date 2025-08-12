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

// TODO needs version protection to keep node valid
struct OwningNodeCursor
{
    Node *node = nullptr;
    unsigned prefix_index{0};

    constexpr OwningNodeCursor()
        : node{nullptr}
        , prefix_index{0}
    {
    }

    constexpr OwningNodeCursor(Node &node_, unsigned prefix_index_ = 0)
        : node{&node_}
        , prefix_index{prefix_index_}
    {
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }
};

MONAD_MPT2_NAMESPACE_END
