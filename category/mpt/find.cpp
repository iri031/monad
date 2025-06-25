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

#include <category/core/assert.h>
#include <category/core/nibble.h>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/trie.hpp>

#include <bit>
#include <cassert>
#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

find_cursor_result_type find_blocking(
    UpdateAuxImpl const &aux, NodeCursor const root, NibblesView const key,
    uint64_t const version)
{
    auto g(aux.shared_lock());
    if (!root.is_valid()) {
        return {NodeCursor{}, find_result::root_node_is_null_failure};
    }
    Node *node = root.node;
    auto &machine = root.machine;
    unsigned node_prefix_index = root.prefix_index;
    unsigned prefix_index = 0;
    while (prefix_index < key.nibble_size()) {
        unsigned char const nibble = key.get(prefix_index);
        root.machine->down(nibble);
        if (node->path_nibbles_len() == node_prefix_index) {
            if (!(node->mask & (1u << nibble))) {
                return {
                    NodeCursor{machine->clone(), *node, node_prefix_index},
                    find_result::branch_not_exist_failure};
            }
            unsigned const child_index = node->to_child_index(nibble);
            if (aux.is_on_disk()) {
                auto const offset = node->fnext(child_index);
                auto const list_type =
                    aux.db_metadata()->at(offset.id)->which_list();
                if (machine->auto_expire()) {
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
                        Node::UniquePtr next_node_ondisk = read_node_blocking(
                            aux, node->fnext(child_index), version);
                        if (!next_node_ondisk) {
                            return {
                                NodeCursor{},
                                find_result::version_no_longer_exist};
                        }
                        node->set_next(
                            child_index, std::move(next_node_ondisk));
                    }
                }
            }
            node_prefix_index = node->next_relpath_start_index();
            ++prefix_index;
            MONAD_ASSERT(node->next(child_index));
            node = node->next(child_index);
            continue;
        }
        if (nibble != node->path_nibble_view().get(node_prefix_index)) {
            // return the last matched node and first mismatch prefix index
            return {
                NodeCursor{machine->clone(), *node, node_prefix_index},
                find_result::key_mismatch_failure};
        }
        // nibble matches
        ++prefix_index;
        ++node_prefix_index;
    }
    if (node_prefix_index != node->path_nibbles_len()) {
        // prefix key exists but no leaf ends at `key`
        return {
            NodeCursor{machine->clone(), *node, node_prefix_index},
            find_result::key_ends_earlier_than_node_failure};
    }
    return {
        NodeCursor{machine->clone(), *node, node_prefix_index},
        find_result::success};
}

MONAD_MPT_NAMESPACE_END
