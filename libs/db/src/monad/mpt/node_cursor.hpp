#pragma once
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>

#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

struct NodeCursor
{
    Node *node{nullptr};
    unsigned prefix_index{0};

    constexpr NodeCursor()
        : node{nullptr}
        , prefix_index{0}
    {
    }

    constexpr NodeCursor(Node &node_, unsigned prefix_index_)
        : node{&node_}
        , prefix_index{prefix_index_}
    {
    }

    constexpr NodeCursor(Node &node_)
        : NodeCursor{node_, node_.bitpacked.path_nibble_index_start}
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

struct OwningNodeCursor
{
    std::shared_ptr<Node> node{nullptr};
    unsigned prefix_index{0};

    constexpr OwningNodeCursor()
        : node{nullptr}
        , prefix_index{0}
    {
    }

    OwningNodeCursor(std::shared_ptr<Node> node_, unsigned prefix_index_)
        : node{node_}
        , prefix_index{prefix_index_}
    {
    }

    explicit OwningNodeCursor(std::shared_ptr<Node> node_)
        : OwningNodeCursor{
              node_, node_ ? node_->bitpacked.path_nibble_index_start : 0u}
    {
    }

    constexpr bool is_valid() const noexcept
    {
        return node != nullptr;
    }

    OwningNodeCursor(OwningNodeCursor &) = default;
    OwningNodeCursor &operator=(OwningNodeCursor &) = default;
    OwningNodeCursor(OwningNodeCursor &&) = default;
    OwningNodeCursor &operator=(OwningNodeCursor &&) = default;
};

static_assert(sizeof(OwningNodeCursor) == 24);
static_assert(alignof(OwningNodeCursor) == 8);

MONAD_MPT_NAMESPACE_END
