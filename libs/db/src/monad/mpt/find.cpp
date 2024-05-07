#include <monad/core/assert.h>
#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

#include <bit>
#include <cassert>

MONAD_MPT_NAMESPACE_BEGIN

find_result_type find_blocking(
    UpdateAuxImpl const &aux, NodeCursor root, NibblesView const key,
    bool in_memory_only)
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
        if (node->path_nibble_index_end == node_prefix_index) {
            if (!(node->mask & (1u << nibble))) {
                return {
                    NodeCursor{*node, node_prefix_index},
                    find_result::branch_not_exist_failure};
            }
            // go to node's matched child
            if (!node->next(node->to_child_index(nibble))) {
                MONAD_ASSERT(aux.is_on_disk());
                if (in_memory_only) {
                    return {
                        NodeCursor{*node, node_prefix_index},
                        find_result::need_to_read_from_disk};
                }

                auto g2(g.upgrade());
                if (g2.upgrade_was_atomic() ||
                    !node->next(node->to_child_index(nibble))) {
                    // read node if not yet in mem
                    node->set_next(
                        node->to_child_index(nibble),
                        read_node_blocking(
                            aux.io->storage_pool(),
                            node->fnext(node->to_child_index(nibble))));
                }
            }
            MONAD_ASSERT(node->next(node->to_child_index(nibble)));
            node = node->next(node->to_child_index(nibble));
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
        // nibble is matched
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

Nibbles find_min_key_blocking(UpdateAuxImpl const &aux, Node &root)
{
    auto g(aux.shared_lock());
    Nibbles path;
    Node *node = &root;
    while (!node->has_value()) {
        MONAD_DEBUG_ASSERT(node->number_of_children() > 0);
        path = concat(
            NibblesView{path},
            node->path_nibble_view(),
            static_cast<unsigned char>(std::countr_zero(node->mask)));
        // go to next node
        if (!node->next(0)) {
            MONAD_ASSERT(aux.is_on_disk());
            auto g2(g.upgrade());
            if (g2.upgrade_was_atomic() || !node->next(0)) {
                node->set_next(
                    0,
                    read_node_blocking(aux.io->storage_pool(), node->fnext(0)));
            }
        }
        MONAD_ASSERT(node->next(0));
        node = node->next(0);
    }
    return concat(NibblesView{path}, node->path_nibble_view());
}

Nibbles find_max_key_blocking(UpdateAuxImpl const &aux, Node &root)
{
    auto g(aux.shared_lock());
    Nibbles path;
    Node *node = &root;
    while (!node->has_value()) {
        MONAD_DEBUG_ASSERT(node->number_of_children() > 0);
        path = concat(
            NibblesView{path},
            node->path_nibble_view(),
            static_cast<unsigned char>(15 - std::countl_zero(node->mask)));
        // go to next node
        if (!node->next(node->number_of_children() - 1)) {
            MONAD_ASSERT(aux.is_on_disk());
            auto g2(g.upgrade());
            if (g2.upgrade_was_atomic() ||
                !node->next(node->number_of_children() - 1)) {
                node->set_next(
                    node->number_of_children() - 1,
                    read_node_blocking(
                        aux.io->storage_pool(),
                        node->fnext(node->number_of_children() - 1)));
            }
        }
        MONAD_ASSERT(node->next(node->number_of_children() - 1));
        node = node->next(node->number_of_children() - 1);
    }
    return concat(NibblesView{path}, node->path_nibble_view());
}

MONAD_MPT_NAMESPACE_END
