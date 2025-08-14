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

#include <category/mpt/trie.hpp>

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io_senders.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/nibble.h>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/request.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/upward_tnode.hpp>
#include <category/mpt/util.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <bit>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <tuple>
#include <utility>
#include <vector>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

/* Names: `prefix_index` is nibble index in prefix of an update,
 `old_prefix_index` is nibble index of path in previous node - old.
 `*_prefix_index_start` is the starting nibble index in current function frame
*/
void dispatch_updates_impl_(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    Node::UniquePtr old, Requests &, unsigned relpath_start_index,
    unsigned prefix_index, NibblesView path,
    std::optional<byte_string_view> opt_leaf_data, int64_t version,
    bool end_of_path = false);

void mismatch_handler_(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    Node::UniquePtr old, SubtrieMetadata, Requests &, NibblesView path,
    unsigned relpath_start_index, unsigned prefix_index);

void create_new_trie_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, UpdateList &&updates, unsigned prefix_index = 0);

void create_new_trie_from_requests_(
    UpdateAuxImpl &, StateMachine &, int64_t &parent_version, ChildData &,
    Requests &, NibblesView path, unsigned relpath_start_index,
    unsigned prefix_index, std::optional<byte_string_view> opt_leaf_data,
    int64_t version, bool end_of_path = false);

void upsert_(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    Node::UniquePtr old, SubtrieMetadata, UpdateList &&,
    unsigned prefix_index = 0);

void create_node_compute_data_possibly_async(
    UpdateAuxImpl &, StateMachine &, UpdateTNode &parent, ChildData &,
    tnode_unique_ptr, bool might_on_disk = true);

void compact_(
    UpdateAuxImpl &, StateMachine &, CompactTNode::unique_ptr_type,
    chunk_offset_t node_offset, bool copy_node_for_fast_or_slow);

void try_fillin_parent_with_rewritten_node(
    UpdateAuxImpl &, CompactTNode::unique_ptr_type);

struct async_write_node_result
{
    chunk_offset_t offset_written_to;
    unsigned bytes_appended;
    erased_connected_operation *io_state;
};

bool verify_node_offset_is_valid(
    UpdateAuxImpl &aux, StateMachine &sm, chunk_offset_t const node_offset,
    int64_t const node_version)
{
    if (!sm.auto_expire()) {
        return true;
    }
    auto const is_valid =
        node_version >=
        static_cast<int64_t>(aux.db_history_min_valid_version());
    if (is_valid) {
        auto const chunk_type =
            aux.db_metadata()->at(node_offset.id)->which_list();
        MONAD_ASSERT(chunk_type == chunk_list::expire);
        MONAD_ASSERT(
            aux.physical_to_virtual(node_offset) >=
            aux.get_min_virtual_expire_offset_metadata());
    }
    return is_valid;
}

// invoke at the end of each block upsert
void flush_buffered_writes(UpdateAuxImpl &);

chunk_offset_t write_new_root_node(UpdateAuxImpl &, Node &, uint64_t);

Node::UniquePtr upsert(
    UpdateAuxImpl &aux, uint64_t const version, StateMachine &sm,
    Node::UniquePtr old, UpdateList &&updates, bool const write_root)
{
    auto impl = [&] {
        aux.reset_stats();
        auto sentinel = make_tnode(1 /*mask*/);
        ChildData &entry = sentinel->children[0];
        sentinel->children[0] = ChildData{.branch = 0};
        if (old) {
            if (updates.empty()) {
                auto const old_path = old->path_nibble_view();
                auto const old_path_nibbles_len = old_path.nibble_size();
                for (unsigned n = 0; n < old_path_nibbles_len; ++n) {
                    sm.down(old_path.get(n));
                }
                // simply dispatch empty update and potentially do compaction
                Requests requests;
                Node const &old_node = *old;
                dispatch_updates_impl_(
                    aux,
                    sm,
                    *sentinel,
                    entry,
                    std::move(old),
                    requests,
                    0, /* relpath_start_index */
                    old_path_nibbles_len, /* prefix_index */
                    old_path,
                    old_node.opt_value(),
                    static_cast<int64_t>(version));
                sm.up(old_path_nibbles_len);
            }
            else {
                SubtrieMetadata old_metadata{};
                old_metadata.version = calc_max_subtrie_version(*old);
                old_metadata.min_version = calc_min_version(*old);
                upsert_(
                    aux,
                    sm,
                    *sentinel,
                    entry,
                    std::move(old),
                    old_metadata,
                    std::move(updates));
            }
            if (sentinel->npending) {
                aux.io->flush();
                MONAD_ASSERT(sentinel->npending == 0);
            }
        }
        else {
            create_new_trie_(
                aux, sm, sentinel->version, entry, std::move(updates));
        }
        auto root = std::move(entry.ptr);
        if (aux.is_on_disk() && root) {
            if (write_root) {
                write_new_root_node(aux, *root, version);
            }
            else {
                flush_buffered_writes(aux);
            }
        }
        return root;
    };
    if (aux.is_current_thread_upserting()) {
        return impl();
    }
    else {
        auto g(aux.unique_lock());
        auto g2(aux.set_current_upsert_tid());
        return impl();
    }
}

struct load_all_impl_
{
    UpdateAuxImpl &aux;

    size_t nodes_loaded{0};

    struct receiver_t
    {
        static constexpr bool lifetime_managed_internally = true;

        load_all_impl_ *impl;
        NodeCursor root;
        unsigned const branch_index;
        std::unique_ptr<StateMachine> sm;

        chunk_offset_t rd_offset{0, 0};
        unsigned bytes_to_read;
        uint16_t buffer_off;

        receiver_t(
            load_all_impl_ *impl, NodeCursor root, unsigned char const branch,
            std::unique_ptr<StateMachine> sm)
            : impl(impl)
            , root(root)
            , branch_index(branch)
            , sm(std::move(sm))
        {
            chunk_offset_t const offset = root.node->fnext(branch_index);
            auto const num_pages_to_load_node =
                node_disk_pages_spare_15{offset}.to_pages();
            bytes_to_read =
                static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
            rd_offset = offset;
            auto const new_offset =
                round_down_align<DISK_PAGE_BITS>(offset.offset);
            MONAD_DEBUG_ASSERT(new_offset <= chunk_offset_t::max_offset);
            rd_offset.offset = new_offset & chunk_offset_t::max_offset;
            buffer_off = uint16_t(offset.offset - rd_offset.offset);
        }

        template <class ResultType>
        void set_value(erased_connected_operation *io_state, ResultType buffer_)
        {
            MONAD_ASSERT(buffer_);
            // load node from read buffer
            {
                auto g(impl->aux.unique_lock());
                MONAD_ASSERT(root.node->next(branch_index) == nullptr);
                root.node->set_next(
                    branch_index,
                    detail::deserialize_node_from_receiver_result(
                        std::move(buffer_), buffer_off, io_state));
                impl->nodes_loaded++;
            }
            auto const next_prefix_index =
                root.node->next_relpath_start_index();
            auto *const next_node = root.node->next(branch_index);
            MONAD_ASSERT(next_prefix_index <= next_node->path_nibbles_len());
            impl->process(NodeCursor{*next_node, next_prefix_index}, *sm);
        }
    };

    explicit constexpr load_all_impl_(UpdateAuxImpl &aux)
        : aux(aux)
    {
    }

    void process(NodeCursor const node_cursor, StateMachine &sm)
    {
        Node *const node = node_cursor.node;
        for (auto const [idx, i] : NodeChildrenRange(node->mask)) {
            NibblesView const nv =
                node->path_nibble_view().substr(node_cursor.prefix_index);
            for (uint8_t n = 0; n < nv.nibble_size(); n++) {
                sm.down(nv.get(n));
            }
            sm.down(i);
            if (sm.cache()) {
                auto *const next = node->next(idx);
                if (next == nullptr) {
                    receiver_t receiver(this, *node, uint8_t(idx), sm.clone());
                    async_read(aux, std::move(receiver));
                }
                else {
                    auto const next_prefix_index =
                        node->next_relpath_start_index();
                    MONAD_ASSERT(next_prefix_index <= next->path_nibbles_len());
                    process(NodeCursor{*next, next_prefix_index}, sm);
                }
            }
            sm.up(1 + nv.nibble_size());
        }
    }
};

size_t load_all(UpdateAuxImpl &aux, StateMachine &sm, NodeCursor const root)
{
    load_all_impl_ impl(aux);
    impl.process(root, sm);
    aux.io->wait_until_done();
    return impl.nodes_loaded;
}

/////////////////////////////////////////////////////
// Async read and update
/////////////////////////////////////////////////////

// Upward update until a unfinished parent node. For each tnode, create the
// trie Node when all its children are created
void upward_update(UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode *tnode)
{
    while (!tnode->npending && tnode->parent) {
        MONAD_DEBUG_ASSERT(tnode->children.size()); // not a leaf
        auto *parent = tnode->parent;
        auto &entry = parent->children[tnode->child_index()];
        // put created node and compute to entry in parent
        size_t const level_up = tnode->relpath_size() + !parent->is_sentinel();
        create_node_compute_data_possibly_async(
            aux, sm, *parent, entry, tnode_unique_ptr{tnode});
        sm.up(level_up);
        tnode = parent;
    }
}

struct update_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    UpdateAuxImpl *aux;
    std::unique_ptr<StateMachine> sm;
    UpdateList updates;
    UpdateTNode *parent;
    ChildData &entry;
    SubtrieMetadata subtrie_metadata;
    chunk_offset_t rd_offset;
    unsigned bytes_to_read;
    uint16_t buffer_off;
    uint8_t prefix_index;

    update_receiver(
        UpdateAuxImpl *aux, std::unique_ptr<StateMachine> sm, ChildData &entry,
        SubtrieMetadata const subtrie_metadata, UpdateList &&updates,
        UpdateTNode *parent, unsigned const prefix_index)
        : aux(aux)
        , sm(std::move(sm))
        , updates(std::move(updates))
        , parent(parent)
        , entry(entry)
        , subtrie_metadata(subtrie_metadata)
        , rd_offset(round_down_align<DISK_PAGE_BITS>(subtrie_metadata.offset))
        , prefix_index(static_cast<uint8_t>(prefix_index))
    {
        // prep uring data
        buffer_off =
            uint16_t(subtrie_metadata.offset.offset - rd_offset.offset);
        // spare bits are number of pages needed to load node
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15(rd_offset).to_pages();
        MONAD_DEBUG_ASSERT(
            num_pages_to_load_node <=
            round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
        rd_offset.set_spare(0);
    }

    template <class ResultType>
    void set_value(erased_connected_operation *io_state, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        Node::UniquePtr old = detail::deserialize_node_from_receiver_result(
            std::move(buffer_), buffer_off, io_state);
        // continue recurse down the trie starting from `old`
        upsert_(
            *aux,
            *sm,
            *parent,
            entry,
            std::move(old),
            subtrie_metadata,
            std::move(updates),
            prefix_index);
        sm->up(1);
        upward_update(*aux, *sm, parent);
    }
};

static_assert(sizeof(update_receiver) == 96);
static_assert(alignof(update_receiver) == 8);

struct read_single_child_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    UpdateAuxImpl *aux;
    chunk_offset_t rd_offset;
    UpdateTNode *tnode; // single child tnode
    ChildData &child;
    unsigned bytes_to_read;
    uint16_t buffer_off;
    std::unique_ptr<StateMachine> sm;

    read_single_child_receiver(
        UpdateAuxImpl *const aux, std::unique_ptr<StateMachine> sm,
        UpdateTNode *const tnode, ChildData &child)
        : aux(aux)
        , rd_offset(0, 0)
        , tnode(tnode)
        , child(child)
        , sm(std::move(sm))
    {
        { // some sanity checks
            auto const virtual_child_offset =
                aux->physical_to_virtual(child.metadata.offset);
            MONAD_DEBUG_ASSERT(virtual_child_offset != INVALID_VIRTUAL_OFFSET);
            // child offset is older than current node writer's start offset
            MONAD_DEBUG_ASSERT(
                virtual_child_offset <
                aux->physical_to_virtual(
                    aux->get_writer_of_list(virtual_child_offset.which_list())
                        ->sender()
                        .offset()));
        }
        rd_offset = round_down_align<DISK_PAGE_BITS>(child.metadata.offset);
        rd_offset.set_spare(0);
        buffer_off = uint16_t(child.metadata.offset.offset - rd_offset.offset);
        // spare bits are number of pages needed to load node
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15{child.metadata.offset}.to_pages();
        MONAD_DEBUG_ASSERT(
            num_pages_to_load_node <=
            round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
    }

    template <class ResultType>
    void set_value(erased_connected_operation *io_state, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        // load node from read buffer
        auto *parent = tnode->parent;
        MONAD_DEBUG_ASSERT(parent);
        auto &entry = parent->children[tnode->child_index()];
        MONAD_DEBUG_ASSERT(entry.branch < 16);
        auto &child = tnode->children[bitmask_index(
            tnode->orig_mask,
            static_cast<unsigned>(std::countr_zero(tnode->mask)))];
        child.ptr = detail::deserialize_node_from_receiver_result(
            std::move(buffer_), buffer_off, io_state);
        auto const path_size = tnode->relpath_size();
        create_node_compute_data_possibly_async(
            *aux, *sm, *parent, entry, tnode_unique_ptr{tnode}, false);
        sm->up(path_size + !parent->is_sentinel());
        upward_update(*aux, *sm, parent);
    }
};

static_assert(sizeof(read_single_child_receiver) == 48);
static_assert(alignof(read_single_child_receiver) == 8);

struct compaction_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    UpdateAuxImpl *aux;
    chunk_offset_t rd_offset;
    chunk_offset_t orig_offset;
    CompactTNode::unique_ptr_type tnode;
    unsigned bytes_to_read;
    uint16_t buffer_off;
    std::unique_ptr<StateMachine> sm;
    bool copy_node_for_fast_or_slow;

    compaction_receiver(
        UpdateAuxImpl *aux_, std::unique_ptr<StateMachine> sm_,
        CompactTNode::unique_ptr_type tnode_, chunk_offset_t const offset,
        bool const copy_node_for_fast_or_slow_)
        : aux(aux_)
        , rd_offset({0, 0})
        , orig_offset(offset)
        , tnode(std::move(tnode_))
        , sm(std::move(sm_))
        , copy_node_for_fast_or_slow(copy_node_for_fast_or_slow_)
    {
        MONAD_ASSERT(offset != INVALID_OFFSET);
        MONAD_ASSERT(tnode && tnode->type == tnode_type::compact);
        rd_offset = round_down_align<DISK_PAGE_BITS>(offset);
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15{rd_offset}.to_pages();
        buffer_off = uint16_t(offset.offset - rd_offset.offset);
        MONAD_DEBUG_ASSERT(
            num_pages_to_load_node <=
            round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
        rd_offset.set_spare(0);

        aux->collect_compaction_read_stats(offset, bytes_to_read);
    }

    template <class ResultType>
    void set_value(erased_connected_operation *io_state, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        tnode->update_after_async_read(
            detail::deserialize_node_from_receiver_result(
                std::move(buffer_), buffer_off, io_state));
        auto *parent = tnode->parent;
        compact_(
            *aux,
            *sm,
            std::move(tnode),
            orig_offset,
            copy_node_for_fast_or_slow);
        while (!parent->npending) {
            if (parent->type == tnode_type::update) {
                upward_update(*aux, *sm, (UpdateTNode *)parent);
                return;
            }
            auto *next_parent = parent->parent;
            MONAD_ASSERT(next_parent);
            MONAD_ASSERT(parent->type == tnode_type::compact);
            try_fillin_parent_with_rewritten_node(
                *aux, CompactTNode::unique_ptr_type{parent});
            // go one level up
            parent = next_parent;
        }
    }
};

/////////////////////////////////////////////////////
// Create Node
/////////////////////////////////////////////////////
Node::UniquePtr create_node_from_children_if_any(
    UpdateAuxImpl &aux, StateMachine &sm, uint16_t const orig_mask,
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, bool const end_of_path,
    unsigned const relpath_start_index,
    std::optional<byte_string_view> const leaf_data, int64_t &version)
{
    aux.collect_number_nodes_created_stats();
    // handle non child and single child cases
    auto const number_of_children = static_cast<unsigned>(std::popcount(mask));
    if (number_of_children == 0) {
        return leaf_data.has_value()
                   ? make_node(0, {}, path, end_of_path, leaf_data.value(), {})
                   : Node::UniquePtr{};
    }
    else if (number_of_children == 1 && !leaf_data.has_value()) {
        auto const j = bitmask_index(
            orig_mask, static_cast<unsigned>(std::countr_zero(mask)));
        MONAD_DEBUG_ASSERT(children[j].ptr);
        version = children[j].metadata.version;
        return std::move(children[j].ptr);
    }
    MONAD_DEBUG_ASSERT(
        number_of_children > 1 ||
        (number_of_children == 1 && leaf_data.has_value()));
    // write children to disk, free any if exceeds the cache level limit
    if (aux.is_on_disk()) {
        for (auto &child : children) {
            if (child.is_valid() && child.metadata.offset == INVALID_OFFSET) {
                // write updated node or node to be compacted to disk
                // won't duplicate write of unchanged old child
                MONAD_DEBUG_ASSERT(child.branch < 16);
                MONAD_DEBUG_ASSERT(child.ptr);
                sm.down(child.branch);
                child.metadata.offset = async_write_node_set_spare(
                    aux,
                    *child.ptr,
                    sm.auto_expire() ? chunk_list::expire : chunk_list::fast);
                sm.up(1);
                auto const child_virtual_offset =
                    aux.physical_to_virtual(child.metadata.offset);
                MONAD_DEBUG_ASSERT(
                    child_virtual_offset != INVALID_VIRTUAL_OFFSET);
                std::tie(
                    child.metadata.min_offset_fast,
                    child.metadata.min_offset_slow) =
                    calc_min_offsets(*child.ptr, child_virtual_offset);
                if (sm.compact()) {
                    MONAD_DEBUG_ASSERT(
                        child.metadata.min_offset_fast >=
                        aux.compact_offset_fast);
                    MONAD_DEBUG_ASSERT(
                        child.metadata.min_offset_slow >=
                        aux.compact_offset_slow);
                }
            }
            // apply cache based on state machine state, always cache node that
            // is a single child
            if (child.ptr && number_of_children > 1 && !child.cache_node) {
                child.ptr.reset();
            }
        }
    }
    return create_node_with_children(
        sm.get_compute(),
        mask,
        children,
        path,
        end_of_path,
        relpath_start_index,
        leaf_data);
}

void create_node_compute_data_possibly_async(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    tnode_unique_ptr tnode, bool const might_on_disk)
{
    if (might_on_disk && tnode->number_of_children() == 1) {
        auto &child = tnode->children[bitmask_index(
            tnode->orig_mask,
            static_cast<unsigned>(std::countr_zero(tnode->mask)))];
        if (!child.ptr) {
            MONAD_DEBUG_ASSERT(aux.is_on_disk());
            MONAD_ASSERT(child.metadata.offset != INVALID_OFFSET);
            read_single_child_receiver receiver(
                &aux, sm.clone(), tnode.release(), child);
            async_read(aux, std::move(receiver));
            MONAD_DEBUG_ASSERT(parent.npending);
            return;
        }
    }
    auto node = create_node_from_children_if_any(
        aux,
        sm,
        tnode->orig_mask,
        tnode->mask,
        tnode->children,
        tnode->path,
        tnode->end_of_path,
        tnode->path_start_index,
        tnode->opt_leaf_data,
        tnode->version);
    MONAD_DEBUG_ASSERT(entry.branch < 16);
    if (node) {
        parent.version = std::max(parent.version, tnode->version);
        NibblesView const path = (std::popcount(tnode->mask) == 1)
                                     ? node->path_nibble_view()
                                     : NibblesView{tnode->path};
        entry.finalize(
            std::move(node),
            tnode->version,
            path.substr(tnode->path_start_index),
            sm.get_compute(),
            sm.cache());
    }
    else {
        parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
        entry.erase();
    }
    --parent.npending;
}

void update_value_and_subtrie_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::UniquePtr old, NibblesView const fullpath,
    unsigned const relpath_start_index, Update &update)
{
    if (update.is_deletion()) {
        parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
        entry.erase();
        --parent.npending;
        return;
    }
    // No need to check next is empty or not, following branches will handle it
    Requests requests;
    requests.split_into_sublists(std::move(update.next), 0);
    MONAD_ASSERT(requests.opt_leaf == std::nullopt);
    if (update.incarnation) {
        // handles empty requests sublist too
        create_new_trie_from_requests_(
            aux,
            sm,
            parent.version,
            entry,
            requests,
            fullpath,
            relpath_start_index,
            0,
            update.value,
            update.version,
            true);
        --parent.npending;
    }
    else {
        auto const opt_leaf =
            update.value.has_value() ? update.value : old->opt_value();
        dispatch_updates_impl_(
            aux,
            sm,
            parent,
            entry,
            std::move(old),
            requests,
            relpath_start_index,
            0,
            fullpath,
            opt_leaf,
            update.version,
            true);
    }
    return;
}

/////////////////////////////////////////////////////
// Create a new trie from a list of updates, no incarnation
/////////////////////////////////////////////////////
void create_new_trie_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, UpdateList &&updates, unsigned prefix_index)
{
    if (updates.empty()) {
        return;
    }
    if (updates.size() == 1) {
        Update &update = updates.front();
        MONAD_DEBUG_ASSERT(update.value.has_value());
        auto const &path = update.key;
        auto const relpath = path.substr(prefix_index);
        for (auto i = 0u; i < relpath.nibble_size(); ++i) {
            sm.down(relpath.get(i));
        }
        MONAD_DEBUG_ASSERT(update.value.has_value());
        MONAD_ASSERT(
            !sm.is_variable_length() || update.next.empty(),
            "Invalid update detected: variable-length tables do not "
            "support updates with a next list");
        Requests requests;
        // requests would be empty if update.next is empty
        requests.split_into_sublists(std::move(update.next), 0);
        MONAD_ASSERT(requests.opt_leaf == std::nullopt);
        create_new_trie_from_requests_(
            aux,
            sm,
            parent_version,
            entry,
            requests,
            path,
            prefix_index,
            0,
            update.value,
            update.version,
            true);
        if (relpath.nibble_size()) {
            sm.up(relpath.nibble_size());
        }
        return;
    }
    // Requests contain more than 2 updates
    Requests requests;
    auto const prefix_index_start = prefix_index;
    // Iterate to find the prefix index where update paths diverge due to key
    // termination or branching
    while (true) {
        unsigned const num_branches =
            requests.split_into_sublists(std::move(updates), prefix_index);
        MONAD_ASSERT(num_branches > 0); // because updates.size() > 1
        // sanity checks on user input
        MONAD_ASSERT(
            !requests.opt_leaf || sm.is_variable_length(),
            "Invalid update input: must mark the state machine as "
            "variable-length to allow variable length updates");
        if (num_branches > 1 || requests.opt_leaf) {
            break;
        }
        sm.down(requests.get_first_branch());
        updates = std::move(requests).first_and_only_list();
        ++prefix_index;
    }
    create_new_trie_from_requests_(
        aux,
        sm,
        parent_version,
        entry,
        requests,
        requests.get_first_path().substr(0, prefix_index),
        prefix_index_start,
        prefix_index,
        requests.opt_leaf.and_then(&Update::value),
        requests.opt_leaf.has_value() ? requests.opt_leaf.value().version : 0);
    if (prefix_index_start != prefix_index) {
        sm.up(prefix_index - prefix_index_start);
    }
}

void create_new_trie_from_requests_(
    UpdateAuxImpl &aux, StateMachine &sm, int64_t &parent_version,
    ChildData &entry, Requests &requests, NibblesView const path,
    unsigned const relpath_start_index, unsigned const prefix_index,
    std::optional<byte_string_view> const opt_leaf_data, int64_t version,
    bool const end_of_path)
{
    // version will be updated bottom up
    uint16_t const mask = requests.mask;
    std::vector<ChildData> children(size_t(std::popcount(mask)));
    for (auto const [index, branch] : NodeChildrenRange(mask)) {
        children[index].branch = branch;
        sm.down(branch);
        create_new_trie_(
            aux,
            sm,
            version,
            children[index],
            std::move(requests)[branch],
            prefix_index + 1);
        sm.up(1);
    }
    auto node = create_node_from_children_if_any(
        aux,
        sm,
        mask,
        mask,
        children,
        path,
        end_of_path,
        relpath_start_index,
        opt_leaf_data,
        version);
    MONAD_ASSERT(node);
    parent_version = std::max(parent_version, version);
    entry.finalize(
        std::move(node),
        version,
        path.substr(relpath_start_index),
        sm.get_compute(),
        sm.cache());
}

/////////////////////////////////////////////////////
// Update existing subtrie
/////////////////////////////////////////////////////

void upsert_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::UniquePtr old, SubtrieMetadata const old_branch_metadata,
    UpdateList &&updates, unsigned prefix_index)
{
    MONAD_ASSERT(!updates.empty());
    // Variable-length tables support only a one-time insert; no deletions or
    // further updates are allowed.
    MONAD_ASSERT(
        !sm.is_variable_length(),
        "Invalid update detected: current implementation does not "
        "support updating variable-length tables");
    if (!old) {
        update_receiver receiver(
            &aux,
            sm.clone(),
            entry,
            old_branch_metadata,
            std::move(updates),
            &parent,
            prefix_index);
        async_read(aux, std::move(receiver));
        return;
    }
    auto const prefix_index_start = prefix_index;
    Requests requests;
    while (true) {
        if (updates.size() == 1 &&
            prefix_index == updates.front().key.nibble_size()) {
            auto &update = updates.front();
            MONAD_ASSERT(old->has_value());
            auto const old_path = old->path_nibble_view();
            update_value_and_subtrie_(
                aux,
                sm,
                parent,
                entry,
                std::move(old),
                old_path,
                prefix_index_start,
                update);
            break;
        }
        unsigned const number_of_sublists = requests.split_into_sublists(
            std::move(updates), prefix_index); // NOLINT
        NibblesView const path =
            old->path_nibble_view().substr(0, prefix_index);
        if (prefix_index == old->path_nibbles_len()) { // end of old
            MONAD_ASSERT(
                !requests.opt_leaf.has_value(),
                "Invalid update detected: cannot apply variable-length "
                "updates to a fixed-length table in the database");
            auto const opt_leaf_data = old->opt_value();
            dispatch_updates_impl_(
                aux,
                sm,
                parent,
                entry,
                std::move(old),
                requests,
                prefix_index_start,
                prefix_index,
                path,
                opt_leaf_data,
                old_branch_metadata.version);
            break;
        }
        if (auto old_nibble = old->path_nibble_view().get(prefix_index);
            number_of_sublists == 1 &&
            requests.get_first_branch() == old_nibble) {
            MONAD_DEBUG_ASSERT(requests.opt_leaf == std::nullopt);
            updates = std::move(requests)[old_nibble];
            sm.down(old_nibble);
            ++prefix_index;
            continue;
        }
        // meet a mismatch or split, not till the end of old path
        mismatch_handler_(
            aux,
            sm,
            parent,
            entry,
            std::move(old),
            old_branch_metadata,
            requests,
            path,
            prefix_index_start,
            prefix_index);
        break;
    }
    if (prefix_index_start != prefix_index) {
        sm.up(prefix_index - prefix_index_start);
    }
}

void fillin_entry(
    UpdateAuxImpl &aux, StateMachine &sm, tnode_unique_ptr tnode,
    UpdateTNode &parent, ChildData &entry)
{
    if (tnode->npending) {
        tnode.release();
    }
    else {
        create_node_compute_data_possibly_async(
            aux, sm, parent, entry, std::move(tnode));
    }
}

/* dispatch updates at the end of old node's path. old node may have leaf data,
 * and there might be update to the leaf value. */
void dispatch_updates_impl_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::UniquePtr old_ptr, Requests &requests,
    unsigned const relpath_start_index, unsigned const prefix_index,
    NibblesView const path, std::optional<byte_string_view> const opt_leaf_data,
    int64_t const version, bool const end_of_path)
{
    Node *const old = old_ptr.get();
    uint16_t const orig_mask = old->mask | requests.mask;
    // tnode->version will be updated bottom up
    auto tnode = make_tnode(
        orig_mask,
        &parent,
        entry.branch,
        path,
        relpath_start_index,
        end_of_path,
        version,
        opt_leaf_data,
        opt_leaf_data.has_value() ? std::move(old_ptr) : Node::UniquePtr{});
    MONAD_DEBUG_ASSERT(
        tnode->children.size() == size_t(std::popcount(orig_mask)));
    auto &children = tnode->children;

    for (auto const [index, branch] : NodeChildrenRange(orig_mask)) {
        if ((1 << branch) & requests.mask) {
            children[index].branch = branch;
            sm.down(branch);
            if ((1 << branch) & old->mask &&
                (aux.is_in_memory() ||
                 verify_node_offset_is_valid(
                     aux,
                     sm,
                     old->fnext(old->to_child_index(branch)),
                     old->child_version(old->to_child_index(branch))))) {
                unsigned const old_child_index = old->to_child_index(branch);
                upsert_(
                    aux,
                    sm,
                    *tnode,
                    children[index],
                    old->move_next(old_child_index),
                    SubtrieMetadata{*old, old_child_index},
                    std::move(requests)[branch],
                    prefix_index + 1);
                sm.up(1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[index],
                    std::move(requests)[branch],
                    prefix_index + 1);
                --tnode->npending;
                sm.up(1);
            }
        }
        else if ((1 << branch) & old->mask) {
            auto &child = children[index];
            child.copy_old_child(old, branch);
            sm.down(branch);
            if (aux.is_on_disk() &&
                !verify_node_offset_is_valid(
                    aux, sm, child.metadata.offset, child.metadata.version)) {
                child.erase();
                tnode->mask &= static_cast<uint16_t>(~(1u << branch));
                --tnode->npending;
                sm.up(1);
                continue;
            }
            sm.up(1);
            if (aux.is_on_disk() && sm.compact() &&
                (child.metadata.min_offset_fast < aux.compact_offset_fast ||
                 child.metadata.min_offset_slow < aux.compact_offset_slow)) {
                MONAD_ASSERT(!sm.auto_expire());
                bool const copy_node_for_fast =
                    child.metadata.min_offset_fast < aux.compact_offset_fast;
                auto compact_tnode = CompactTNode::make(
                    tnode.get(), index, std::move(child.ptr));
                compact_(
                    aux,
                    sm,
                    std::move(compact_tnode),
                    child.metadata.offset,
                    copy_node_for_fast);
            }
            else {
                --tnode->npending;
            }
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

// Split `old` at old_prefix_index, `updates` are already splitted at
// prefix_index to `requests`, which can have 1 or more sublists.
void mismatch_handler_(
    UpdateAuxImpl &aux, StateMachine &sm, UpdateTNode &parent, ChildData &entry,
    Node::UniquePtr old_ptr, SubtrieMetadata const old_branch_metadata,
    Requests &requests, NibblesView const path, unsigned relpath_start_index,
    unsigned const prefix_index)
{
    MONAD_ASSERT(old_ptr);
    Node &old = *old_ptr;
    MONAD_DEBUG_ASSERT(old.path_nibbles_len() > relpath_start_index);
    // Note: no leaf can be created at an existing non-leaf node
    MONAD_DEBUG_ASSERT(!requests.opt_leaf.has_value());
    unsigned char const old_nibble = old.path_nibble_view().get(prefix_index);
    uint16_t const orig_mask =
        static_cast<uint16_t>(1u << old_nibble | requests.mask);
    auto tnode =
        make_tnode(orig_mask, &parent, entry.branch, path, relpath_start_index);
    auto const number_of_children =
        static_cast<unsigned>(std::popcount(orig_mask));
    MONAD_DEBUG_ASSERT(
        tnode->children.size() == number_of_children && number_of_children > 0);
    auto &children = tnode->children;

    for (auto const [index, branch] : NodeChildrenRange(orig_mask)) {
        if ((1 << branch) & requests.mask) {
            children[index].branch = branch;
            sm.down(branch);
            if (branch == old_nibble &&
                (aux.is_in_memory() || verify_node_offset_is_valid(
                                           aux,
                                           sm,
                                           old_branch_metadata.offset,
                                           old_branch_metadata.version))) {
                upsert_(
                    aux,
                    sm,
                    *tnode,
                    children[index],
                    std::move(old_ptr),
                    old_branch_metadata,
                    std::move(requests)[branch],
                    prefix_index + 1);
            }
            else {
                create_new_trie_(
                    aux,
                    sm,
                    tnode->version,
                    children[index],
                    std::move(requests)[branch],
                    prefix_index + 1);
                --tnode->npending;
            }
            sm.up(1);
        }
        else if (branch == old_nibble) {
            sm.down(old_nibble);
            if (aux.is_on_disk() && !verify_node_offset_is_valid(
                                        aux,
                                        sm,
                                        old_branch_metadata.offset,
                                        old_branch_metadata.version)) {
                entry.erase();
                parent.mask &= static_cast<uint16_t>(~(1u << old_nibble));
                sm.up(1);
                --tnode->npending;
                continue;
            }
            // nexts[j] is a path-shortened old node, trim prefix
            auto const relpath_start_index = prefix_index + 1;
            NibblesView const child_new_relpath =
                old.path_nibble_view().substr(relpath_start_index);
            for (auto i = 0u; i < child_new_relpath.nibble_size(); ++i) {
                sm.down(child_new_relpath.get(i));
            }
            auto &child = children[index];
            child.recompute_data_with_truncated_path(
                branch,
                std::move(old_ptr),
                old_branch_metadata,
                relpath_start_index,
                sm.get_compute(),
                sm.cache());
            sm.up(child_new_relpath.nibble_size() + 1);
            if (aux.is_on_disk() && sm.compact() &&
                (child.metadata.min_offset_fast < aux.compact_offset_fast ||
                 child.metadata.min_offset_slow < aux.compact_offset_slow)) {
                MONAD_ASSERT(!sm.auto_expire());
                bool const copy_node_for_fast =
                    child.metadata.min_offset_fast < aux.compact_offset_fast;
                auto compact_tnode = CompactTNode::make(
                    tnode.get(), index, std::move(child.ptr));
                compact_(
                    aux,
                    sm,
                    std::move(compact_tnode),
                    INVALID_OFFSET,
                    copy_node_for_fast);
            }
            else {
                --tnode->npending;
            }
        }
    }
    fillin_entry(aux, sm, std::move(tnode), parent, entry);
}

void compact_(
    UpdateAuxImpl &aux, StateMachine &sm, CompactTNode::unique_ptr_type tnode,
    chunk_offset_t const node_offset, bool const copy_node_for_fast_or_slow)
{
    MONAD_ASSERT(sm.compact() && !sm.auto_expire());
    MONAD_ASSERT(tnode->type == tnode_type::compact);
    if (!tnode->node) {
        compaction_receiver receiver(
            &aux,
            sm.clone(),
            std::move(tnode),
            node_offset,
            copy_node_for_fast_or_slow);
        async_read(aux, std::move(receiver));
        return;
    }
    // Only compact nodes < compaction range (either fast or slow) to slow,
    // otherwise rewrite to fast list
    // INVALID_OFFSET indicates node is being updated and not yet written, that
    // case we write to fast
    auto const virtual_node_offset = aux.physical_to_virtual(node_offset);
    MONAD_ASSERT(virtual_node_offset.which_list() != chunk_list::expire);
    bool const rewrite_to_fast = [&aux, &virtual_node_offset] {
        if (virtual_node_offset == INVALID_VIRTUAL_OFFSET) {
            return true;
        }
        compact_virtual_chunk_offset_t const compacted_virtual_offset{
            virtual_node_offset};
        return (virtual_node_offset.which_list() == chunk_list::fast &&
                compacted_virtual_offset >= aux.compact_offset_fast) ||
               (virtual_node_offset.which_list() == chunk_list::slow &&
                compacted_virtual_offset >= aux.compact_offset_slow);
    }();

    Node &node = *tnode->node;
    tnode->rewrite_to_fast = rewrite_to_fast;
    aux.collect_compacted_nodes_stats(
        copy_node_for_fast_or_slow,
        rewrite_to_fast,
        virtual_node_offset,
        node.get_disk_size());

    for (unsigned j = 0; j < node.number_of_children(); ++j) {
        if (node.min_offset_fast(j) < aux.compact_offset_fast ||
            node.min_offset_slow(j) < aux.compact_offset_slow) {
            auto child_tnode =
                CompactTNode::make(tnode.get(), j, node.move_next(j));
            compact_(
                aux,
                sm,
                std::move(child_tnode),
                node.fnext(j),
                node.min_offset_fast(j) < aux.compact_offset_fast);
        }
        else {
            --tnode->npending;
        }
    }
    // Compaction below `node` is completed, rewrite `node` to disk and put
    // offset and min_offset somewhere in parent depends on its type
    try_fillin_parent_with_rewritten_node(aux, std::move(tnode));
}

void try_fillin_parent_with_rewritten_node(
    UpdateAuxImpl &aux, CompactTNode::unique_ptr_type tnode)
{
    if (tnode->npending) { // there are unfinished async below node
        tnode.release();
        return;
    }
    auto [min_offset_fast, min_offset_slow] =
        calc_min_offsets(*tnode->node, INVALID_VIRTUAL_OFFSET);
    // If subtrie contains nodes from fast list, write itself to fast list too
    if (min_offset_fast != INVALID_COMPACT_VIRTUAL_OFFSET) {
        tnode->rewrite_to_fast = true; // override that
    }
    auto const new_offset = async_write_node_set_spare(
        aux,
        *tnode->node,
        tnode->rewrite_to_fast ? chunk_list::fast : chunk_list::slow);
    auto const new_node_virtual_offset = aux.physical_to_virtual(new_offset);
    MONAD_DEBUG_ASSERT(new_node_virtual_offset != INVALID_VIRTUAL_OFFSET);
    compact_virtual_chunk_offset_t const truncated_new_virtual_offset{
        new_node_virtual_offset};
    // update min offsets in subtrie
    if (tnode->rewrite_to_fast) {
        min_offset_fast =
            std::min(min_offset_fast, truncated_new_virtual_offset);
    }
    else {
        min_offset_slow =
            std::min(min_offset_slow, truncated_new_virtual_offset);
    }
    MONAD_DEBUG_ASSERT(min_offset_fast >= aux.compact_offset_fast);
    MONAD_DEBUG_ASSERT(min_offset_slow >= aux.compact_offset_slow);
    auto *parent = tnode->parent;
    auto const index = tnode->index;
    if (parent->type == tnode_type::compact) {
        parent->node->set_fnext(index, new_offset);
        parent->node->set_min_offset_fast(index, min_offset_fast);
        parent->node->set_min_offset_slow(index, min_offset_slow);
        if (tnode->cache_node) {
            parent->node->set_next(index, std::move(tnode->node));
        }
    }
    else { // parent tnode is an update tnode
        auto *const p = reinterpret_cast<UpdateTNode *>(parent);
        MONAD_DEBUG_ASSERT(tnode->cache_node);
        auto &child = p->children[index];
        child.ptr = std::move(tnode->node);
        child.metadata.offset = new_offset;
        child.metadata.min_offset_fast = min_offset_fast;
        child.metadata.min_offset_slow = min_offset_slow;
    }
    --parent->npending;
}

/////////////////////////////////////////////////////
// Async write
/////////////////////////////////////////////////////

node_writer_unique_ptr_type replace_node_writer_to_start_at_new_chunk(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type &node_writer)
{
    auto *sender = &node_writer->sender();
    chunk_list const list_type =
        aux.db_metadata()->at(sender->offset().id)->which_list();
    auto const *ci_ = aux.db_metadata()->free_list_end();
    MONAD_ASSERT(ci_ != nullptr); // we are out of free blocks!
    auto idx = ci_->index(aux.db_metadata());
    chunk_offset_t const offset_of_new_writer{idx, 0};
    // Pad buffer of existing node write that is about to get initiated so it's
    // O_DIRECT i/o aligned
    auto const remaining_buffer_bytes = sender->remaining_buffer_bytes();
    auto *tozero = sender->advance_buffer_append(remaining_buffer_bytes);
    MONAD_DEBUG_ASSERT(tozero != nullptr);
    memset(tozero, 0, remaining_buffer_bytes);

    /* If there aren't enough write buffers, this may poll uring until a free
    write buffer appears. However, that polling may write a node, causing
    this function to be reentered, and another free chunk allocated and now
    writes are being directed there instead. Obviously then replacing that new
    partially filled chunk with this new chunk is something which trips the
    asserts.

    Replacing the runloop exposed this bug much more clearly than before, but we
    had been seeing occasional issues somewhere around here for some time now,
    it just wasn't obvious the cause. Anyway detect when reentrancy occurs, and
    if so undo this operation and tell the caller to retry.
    */
    static thread_local struct reentrancy_detection_t
    {
        int count{0}, max_count{0};
    } reentrancy_detection;

    int const my_reentrancy_count = reentrancy_detection.count++;
    MONAD_ASSERT(my_reentrancy_count >= 0);
    if (my_reentrancy_count == 0) {
        // We are at the base
        reentrancy_detection.max_count = 0;
    }
    else if (my_reentrancy_count > reentrancy_detection.max_count) {
        // We are reentering
        LOG_INFO_CFORMAT(
            "replace_node_writer_to_start_at_new_chunk reenter "
            "my_reentrancy_count = "
            "%d max_count = %d",
            my_reentrancy_count,
            reentrancy_detection.max_count);
        reentrancy_detection.max_count = my_reentrancy_count;
    }
    auto ret = aux.io->make_connected(
        write_single_buffer_sender{
            offset_of_new_writer, AsyncIO::WRITE_BUFFER_SIZE},
        write_operation_io_receiver{AsyncIO::WRITE_BUFFER_SIZE});
    reentrancy_detection.count--;
    MONAD_ASSERT(reentrancy_detection.count >= 0);
    // The deepest-most reentrancy must succeed, and all less deep reentrancies
    // must retry
    if (my_reentrancy_count != reentrancy_detection.max_count) {
        // We reentered, please retry
        LOG_INFO_CFORMAT(
            "replace_node_writer_to_start_at_new_chunk retry "
            "my_reentrancy_count = "
            "%d max_count = %d",
            my_reentrancy_count,
            reentrancy_detection.max_count);
        return {};
    }
    aux.remove(idx);
    aux.append(list_type, idx);
    return ret;
}

node_writer_unique_ptr_type replace_node_writer(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type const &node_writer)
{
    // Can't use add_to_offset(), because it asserts if we go past the
    // capacity
    auto offset_of_next_writer = node_writer->sender().offset();
    chunk_list const list_type =
        aux.db_metadata()->at(offset_of_next_writer.id)->which_list();
    file_offset_t offset = offset_of_next_writer.offset;
    offset += node_writer->sender().written_buffer_bytes();
    offset_of_next_writer.offset = offset & chunk_offset_t::max_offset;
    auto const chunk_capacity =
        aux.io->chunk_capacity(offset_of_next_writer.id);
    MONAD_ASSERT(offset <= chunk_capacity);
    detail::db_metadata::chunk_info_t const *ci_ = nullptr;
    uint32_t idx;
    if (offset == chunk_capacity) {
        // If after the current write buffer we're hitting chunk capacity, we
        // replace writer to the start of next chunk.
        ci_ = aux.db_metadata()->free_list_end();
        MONAD_ASSERT(ci_ != nullptr); // we are out of free blocks!
        idx = ci_->index(aux.db_metadata());
        offset_of_next_writer.id = idx & 0xfffffU;
        offset_of_next_writer.offset = 0;
    }
    // See above about handling potential reentrancy correctly
    auto *const node_writer_ptr = node_writer.get();
    size_t const bytes_to_write = std::min(
        AsyncIO::WRITE_BUFFER_SIZE,
        (size_t)(chunk_capacity - offset_of_next_writer.offset));
    auto ret = aux.io->make_connected(
        write_single_buffer_sender{offset_of_next_writer, bytes_to_write},
        write_operation_io_receiver{bytes_to_write});
    if (node_writer.get() != node_writer_ptr) {
        // We reentered, please retry
        return {};
    }
    if (ci_ != nullptr) {
        MONAD_DEBUG_ASSERT(ci_ == aux.db_metadata()->free_list_end());
        aux.remove(idx);
        aux.append(list_type, idx);
    }
    return ret;
}

// return physical offset the node is written at
async_write_node_result async_write_node(
    UpdateAuxImpl &aux, node_writer_unique_ptr_type &node_writer,
    Node const &node)
{
retry:
    aux.io->poll_nonblocking_if_not_within_completions(1);
    auto *sender = &node_writer->sender();
    auto const size = node.get_disk_size();
    auto const remaining_bytes = sender->remaining_buffer_bytes();
    async_write_node_result ret{
        .offset_written_to = INVALID_OFFSET,
        .bytes_appended = size,
        .io_state = node_writer.get()};
    [[likely]] if (size <= remaining_bytes) { // Node can fit into current
                                              // buffer
        ret.offset_written_to =
            sender->offset().add_to_offset(sender->written_buffer_bytes());
        auto *where_to_serialize = sender->advance_buffer_append(size);
        MONAD_DEBUG_ASSERT(where_to_serialize != nullptr);
        serialize_node_to_buffer(
            (unsigned char *)where_to_serialize, size, node, size);
    }
    else {
        auto const chunk_remaining_bytes =
            aux.io->chunk_capacity(sender->offset().id) -
            sender->offset().offset - sender->written_buffer_bytes();
        node_writer_unique_ptr_type new_node_writer{};
        unsigned offset_in_on_disk_node = 0;
        if (size > chunk_remaining_bytes) {
            // Node won't fit in the rest of current chunk, start at a new chunk
            new_node_writer =
                replace_node_writer_to_start_at_new_chunk(aux, node_writer);
            if (!new_node_writer) {
                goto retry;
            }
            ret.offset_written_to = new_node_writer->sender().offset();
        }
        else {
            // serialize node to current writer's remaining bytes because node
            // serialization will not cross chunk boundary
            ret.offset_written_to =
                sender->offset().add_to_offset(sender->written_buffer_bytes());
            auto bytes_to_append = std::min(
                (unsigned)remaining_bytes, size - offset_in_on_disk_node);
            auto *where_to_serialize =
                (unsigned char *)node_writer->sender().advance_buffer_append(
                    bytes_to_append);
            MONAD_DEBUG_ASSERT(where_to_serialize != nullptr);
            serialize_node_to_buffer(
                where_to_serialize,
                bytes_to_append,
                node,
                size,
                offset_in_on_disk_node);
            offset_in_on_disk_node += bytes_to_append;
            new_node_writer = replace_node_writer(aux, node_writer);
            if (!new_node_writer) {
                goto retry;
            }
            MONAD_DEBUG_ASSERT(
                new_node_writer->sender().offset().id ==
                node_writer->sender().offset().id);
        }
        // initiate current node writer
        if (node_writer->sender().written_buffer_bytes() !=
            node_writer->sender().buffer().size()) {
            LOG_INFO_CFORMAT(
                "async_write_node %zu != %zu",
                node_writer->sender().written_buffer_bytes(),
                node_writer->sender().buffer().size());
        }
        MONAD_ASSERT(
            node_writer->sender().written_buffer_bytes() ==
            node_writer->sender().buffer().size());
        node_writer->initiate();
        // shall be recycled by the i/o receiver
        node_writer.release();
        node_writer = std::move(new_node_writer);
        // serialize the rest of the node to buffer
        while (offset_in_on_disk_node < size) {
            auto *where_to_serialize =
                (unsigned char *)node_writer->sender().buffer().data();
            auto bytes_to_append = std::min(
                (unsigned)node_writer->sender().remaining_buffer_bytes(),
                size - offset_in_on_disk_node);
            serialize_node_to_buffer(
                where_to_serialize,
                bytes_to_append,
                node,
                size,
                offset_in_on_disk_node);
            offset_in_on_disk_node += bytes_to_append;
            MONAD_ASSERT(offset_in_on_disk_node <= size);
            MONAD_ASSERT(
                node_writer->sender().advance_buffer_append(bytes_to_append) !=
                nullptr);
            if (offset_in_on_disk_node < size &&
                node_writer->sender().remaining_buffer_bytes() == 0) {
                // replace node writer
                new_node_writer = replace_node_writer(aux, node_writer);
                if (new_node_writer) {
                    // initiate current node writer
                    MONAD_DEBUG_ASSERT(
                        node_writer->sender().written_buffer_bytes() ==
                        node_writer->sender().buffer().size());
                    node_writer->initiate();
                    // shall be recycled by the i/o receiver
                    node_writer.release();
                    node_writer = std::move(new_node_writer);
                }
            }
        }
    }
    return ret;
}

// Return node's physical offset the node is written at, triedb should not
// depend on any metadata to walk the data structure.
chunk_offset_t
async_write_node_set_spare(UpdateAuxImpl &aux, Node &node, chunk_list list_type)
{
    if (!aux.can_write_to_fast() && list_type == chunk_list::fast) {
        list_type = chunk_list::slow;
    }
    if (list_type != chunk_list::expire && aux.alternate_slow_fast_writer()) {
        // alternate between slow and fast writer
        aux.set_can_write_to_fast(!aux.can_write_to_fast());
    }

    auto off = async_write_node(aux, aux.get_writer_of_list(list_type), node)
                   .offset_written_to;
    MONAD_ASSERT(list_type == aux.db_metadata()->at(off.id)->which_list());
    unsigned const pages = num_pages(off.offset, node.get_disk_size());
    off.set_spare(static_cast<uint16_t>(node_disk_pages_spare_15{pages}));
    return off;
}

void flush_buffered_writes(UpdateAuxImpl &aux)
{
    // Round up with all bits zero
    auto replace = [&](node_writer_unique_ptr_type &node_writer) {
        auto *sender = &node_writer->sender();
        auto written = sender->written_buffer_bytes();
        auto paddedup = round_up_align<DISK_PAGE_BITS>(written);
        auto const tozerobytes = paddedup - written;
        auto *tozero = sender->advance_buffer_append(tozerobytes);
        MONAD_DEBUG_ASSERT(tozero != nullptr);
        memset(tozero, 0, tozerobytes);
        // replace fast node writer
        auto new_node_writer = replace_node_writer(aux, node_writer);
        while (!new_node_writer) {
            new_node_writer = replace_node_writer(aux, node_writer);
        }
        auto to_initiate = std::move(node_writer);
        node_writer = std::move(new_node_writer);
        to_initiate->receiver().reset(
            to_initiate->sender().written_buffer_bytes());
        to_initiate->initiate();
        // shall be recycled by the i/o receiver
        to_initiate.release();
    };
    if (aux.node_writer_fast->sender().written_buffer_bytes()) {
        replace(aux.node_writer_fast);
    }
    if (aux.node_writer_slow->sender().written_buffer_bytes()) {
        replace(aux.node_writer_slow);
    }
    if (aux.node_writer_expire->sender().written_buffer_bytes()) {
        replace(aux.node_writer_expire);
    }
    aux.io->flush();
}

// return root physical offset
chunk_offset_t
write_new_root_node(UpdateAuxImpl &aux, Node &root, uint64_t const version)
{
    auto const offset_written_to =
        async_write_node_set_spare(aux, root, chunk_list::fast);
    flush_buffered_writes(aux);
    // advance fast and slow ring's latest offset in db metadata
    aux.advance_db_offsets_to(
        aux.node_writer_fast->sender().offset(),
        aux.node_writer_slow->sender().offset(),
        aux.node_writer_expire->sender().offset());
    // update root offset
    auto const max_version_in_db = aux.db_history_max_version();
    if (MONAD_UNLIKELY(max_version_in_db == INVALID_BLOCK_NUM)) {
        aux.fast_forward_next_version(version);
        aux.append_root_offset(offset_written_to);
        MONAD_ASSERT(aux.db_history_range_lower_bound() == version);
    }
    else if (version <= max_version_in_db) {
        MONAD_ASSERT(
            version >=
            ((max_version_in_db >= aux.version_history_length())
                 ? max_version_in_db - aux.version_history_length() + 1
                 : 0));
        auto const prev_lower_bound = aux.db_history_range_lower_bound();
        aux.update_root_offset(version, offset_written_to);
        MONAD_ASSERT(
            aux.db_history_range_lower_bound() ==
            std::min(version, prev_lower_bound));
    }
    else {
        MONAD_ASSERT(version == max_version_in_db + 1);
        aux.append_root_offset(offset_written_to);
    }
    return offset_written_to;
}

MONAD_MPT_NAMESPACE_END
