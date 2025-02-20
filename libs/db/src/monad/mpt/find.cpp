#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/node_cursor.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/trie.hpp>

#include <bit>
#include <cassert>
#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

find_cursor_result_type find_blocking(
    UpdateAuxImpl const &aux, NodeCursor root, NibblesView const key,
    uint64_t const version, StateMachine &machine)
{
    auto g(aux.shared_lock());
    if (!root.is_valid()) {
        return {NodeCursor{}, find_result::root_node_is_null_failure};
    }
    Node *node = root.node;
    unsigned node_prefix_index = root.prefix_index;
    unsigned prefix_index = 0;
    while (prefix_index < key.nibble_size()) {
        unsigned char const nibble = key.get(prefix_index);
        machine.down(nibble);
        if (node->path_nibble_index_end == node_prefix_index) {
            if (!(node->mask & (1u << nibble))) {
                return {
                    NodeCursor{*node, node_prefix_index},
                    find_result::branch_not_exist_failure};
            }
            unsigned const child_index = node->to_child_index(nibble);
            if (aux.is_on_disk()) {
                auto const offset = node->fnext(child_index);
                auto const list_type =
                    aux.db_metadata()->at(offset.id)->which_list();
                if (machine.auto_expire()) {
                    if (list_type != chunk_list::expire ||
                        aux.physical_to_virtual(offset) <
                            aux.get_min_virtual_expire_offset_metadata()) {
                        return {
                            NodeCursor{},
                            find_result::node_is_pruned_by_auto_expiration};
                    }
                }
                else {
                    MONAD_ASSERT(
                        list_type != chunk_list::expire &&
                        list_type != chunk_list::free);
                }
                // go to node's matched child
                if (!node->next(child_index)) {
                    auto g2(g.upgrade());
                    if (g2.upgrade_was_atomic() || !node->next(child_index)) {
                        node->set_next(
                            child_index,
                            read_node_blocking(aux, offset, version));
                    }
                }
            }
            MONAD_ASSERT(node->next(child_index));
            node = node->next(child_index);
            node_prefix_index = node->bitpacked.path_nibble_index_start;
            ++prefix_index;
            continue;
        }
        if (nibble != get_nibble(node->path_data(), node_prefix_index)) {
            // return the last matched node and first mismatch prefix index
            return {
                NodeCursor{*node, node_prefix_index},
                find_result::key_mismatch_failure};
        }
        // nibble matches
        ++prefix_index;
        ++node_prefix_index;
    }
    if (node_prefix_index != node->path_nibble_index_end) {
        // prefix key exists but no leaf ends at `key`
        return {
            NodeCursor{*node, node_prefix_index},
            find_result::key_ends_earlier_than_node_failure};
    }
    return {NodeCursor{*node, node_prefix_index}, find_result::success};
}

MONAD_MPT_NAMESPACE_END
