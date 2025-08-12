#pragma once

#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/core/tl_tid.h>
#include <category/mpt2/config.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/util.hpp>

#include <cstdint>
#include <functional>

#include <boost/container/deque.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

struct TraverseMachine
{
    size_t level{0};

    virtual ~TraverseMachine() = default;
    // Implement the logic to decide when to stop, return true for continue,
    // false for stop
    virtual bool down(unsigned char branch, Node const &) = 0;
    virtual void up(unsigned char branch, Node const &) = 0;
    virtual std::unique_ptr<TraverseMachine> clone() const = 0;

    virtual bool should_visit(Node const &, unsigned char)
    {
        return true;
    }
};

// TODO: move definitions out of header file
namespace detail
{
    inline bool preorder_traverse_blocking_impl(
        UpdateAux &aux, unsigned char const branch, Node const &node,
        TraverseMachine &traverse, uint64_t const version)
    {
        ++traverse.level;
        if (!traverse.down(branch, node)) {
            --traverse.level;
            return true;
        }
        for (auto const [idx, branch] : NodeChildrenRange(node.mask)) {
            if (traverse.should_visit(node, branch)) {
                auto next_offset = node.fnext(idx);
                if (next_offset != INVALID_OFFSET) {
                    auto next_node = aux.parse_node(next_offset);
                    if (!preorder_traverse_blocking_impl(
                            aux, branch, *next_node, traverse, version)) {
                        return false;
                    }
                }
            }
        }
        --traverse.level;
        traverse.up(branch, node);
        return true;
    }
}

// return value indicates if we have done the full traversal or not
inline bool preorder_traverse_blocking(
    UpdateAuxImpl &aux, Node const &node, TraverseMachine &traverse,
    uint64_t const version)
{
    return detail::preorder_traverse_blocking_impl(
        aux, INVALID_BRANCH, node, traverse, version);
}

MONAD_MPT2_NAMESPACE_END
