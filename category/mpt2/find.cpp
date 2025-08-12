#include <category/core/assert.h>
#include <category/core/nibble.h>
#include <category/mpt2/config.hpp>
#include <category/mpt2/nibbles_view.hpp>
#include <category/mpt2/node_cursor.hpp>
#include <category/mpt2/trie.hpp>

#include <bit>
#include <cassert>
#include <cstdint>

MONAD_MPT2_NAMESPACE_BEGIN

find_cursor_result_type find(
    UpdateAux const &aux, NodeCursor const root, NibblesView const key,
    uint64_t const)
{
    // TODO: verify version is valid during the find
    Node *node = root.node;
    unsigned node_prefix_index = root.prefix_index;
    unsigned prefix_index = 0;
    while (prefix_index < key.nibble_size()) {
        unsigned char const nibble = key.get(prefix_index);
        if (node->path_nibbles_len() == node_prefix_index) {
            if (!(node->mask & (1u << nibble))) {
                return {
                    NodeCursor{*node, node_prefix_index},
                    find_result::branch_not_exist_failure};
            }
            node = aux.parse_node(node->fnext(node->to_child_index(nibble)));
            node_prefix_index = 0;
            ++prefix_index;
            continue;
        }
        if (nibble != node->path_nibble_view().get(node_prefix_index)) {
            // return the last matched node and first mismatch prefix index
            return {
                NodeCursor{*node, node_prefix_index},
                find_result::key_mismatch_failure};
        }
        // nibble is matched
        ++prefix_index;
        ++node_prefix_index;
    }
    if (node_prefix_index != node->path_nibbles_len()) {
        // prefix key exists but no leaf ends at `key`
        return {
            NodeCursor{*node, node_prefix_index},
            find_result::key_ends_earlier_than_node_failure};
    }
    return {NodeCursor{*node, node_prefix_index}, find_result::success};
}

MONAD_MPT2_NAMESPACE_END
