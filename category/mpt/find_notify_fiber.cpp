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

#include <category/async/config.hpp>

#include <category/async/concepts.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/core/nibble.h>
#include <category/core/tl_tid.h>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/boost_fiber_workarounds.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <boost/fiber/future.hpp>

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <limits>
#include <memory>
#include <utility>

#include <unistd.h>

#include "deserialize_node_from_receiver_result.hpp"

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

namespace
{
    struct find_receiver
    {
        static constexpr bool lifetime_managed_internally = true;

        UpdateAuxImpl *aux;
        inflight_map_t &inflights;
        Node *parent;
        chunk_offset_t rd_offset; // required for sender
        unsigned bytes_to_read; // required for sender too
        uint16_t buffer_off;
        unsigned const branch_index;
        std::unique_ptr<StateMachine> machine;

        find_receiver(
            UpdateAuxImpl &aux, inflight_map_t &inflights, Node *const parent,
            unsigned char const branch, std::unique_ptr<StateMachine> machine)
            : aux(&aux)
            , inflights(inflights)
            , parent(parent)
            , rd_offset(0, 0)
            , branch_index(parent->to_child_index(branch))
            , machine(std::move(machine))
        {
            MONAD_ASSERT(this->machine != nullptr);
            chunk_offset_t const offset = parent->fnext(branch_index);
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

        //! notify a list of requests pending on this node
        template <class ResultType>
        void set_value(
            MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
            ResultType buffer_)
        {
            MONAD_ASSERT(buffer_);
            auto const offset = parent->fnext(branch_index);
            auto *node = parent->next(branch_index);
            if (node == nullptr) {
                parent->set_next(
                    branch_index,
                    detail::deserialize_node_from_receiver_result(
                        std::move(buffer_), buffer_off, io_state));
                node = parent->next(branch_index);
            }
            auto it = inflights.find(offset);
            if (it != inflights.end()) {
                auto pendings = std::move(it->second);
                inflights.erase(it);
                for (auto &cont : pendings) {
                    MONAD_ASSERT(cont(*node, machine->clone()));
                }
            }
        }
    };

    struct find_owning_receiver
    {
        static constexpr bool lifetime_managed_internally = true;

        UpdateAuxImpl *aux;
        NodeCache &node_cache;
        inflight_map_owning_t &inflights;
        chunk_offset_t offset;
        virtual_chunk_offset_t virtual_offset;
        chunk_offset_t rd_offset; // required for sender
        unsigned bytes_to_read; // required for sender too
        uint16_t buffer_off;
        std::unique_ptr<StateMachine> machine;

        find_owning_receiver(
            UpdateAuxImpl &aux, NodeCache &node_cache,
            inflight_map_owning_t &inflights, chunk_offset_t const offset,
            virtual_chunk_offset_t const virtual_offset,
            std::unique_ptr<StateMachine> machine)
            : aux(&aux)
            , node_cache(node_cache)
            , inflights(inflights)
            , offset(offset)
            , virtual_offset(virtual_offset)
            , rd_offset(0, 0)
            , machine(std::move(machine))
        {
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

        //! notify a list of requests pending on this node
        template <class ResultType>
        void set_value(
            MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
            ResultType buffer_)
        {
            MONAD_ASSERT(buffer_);
            std::shared_ptr<Node> next_node;
            // verify the offset it read is still valid and has not been reused
            // to write new data.
            auto const virtual_offset_after = aux->physical_to_virtual(offset);
            if (virtual_offset_after == virtual_offset) {
                {
                    NodeCache::ConstAccessor acc;
                    MONAD_ASSERT(node_cache.find(acc, virtual_offset) == false);
                }
                next_node = detail::deserialize_node_from_receiver_result(
                    std::move(buffer_), buffer_off, io_state);
                node_cache.insert(virtual_offset, next_node);
            }
            auto it = inflights.find(virtual_offset);
            MONAD_ASSERT(it != inflights.end());
            auto pendings = std::move(it->second);
            inflights.erase(it);
            for (auto &cont : pendings) {
                MONAD_ASSERT(
                    cont(next_node, machine ? machine->clone() : nullptr));
            }
        }
    };

    void async_read_with_continuation(
        UpdateAuxImpl &aux, NodeCache &node_cache,
        inflight_map_owning_t &inflights,
        threadsafe_boost_fibers_promise<find_owning_cursor_result_type>
            &promise,
        auto &&cont, chunk_offset_t const read_offset,
        virtual_chunk_offset_t const virtual_offset,
        std::unique_ptr<StateMachine> machine)
    {
        if (aux.io->owning_thread_id() != get_tl_tid()) {
            promise.set_value(
                {OwningNodeCursor{},
                 find_result::need_to_continue_in_io_thread});
            return;
        }
        if (auto lt = inflights.find(virtual_offset); lt != inflights.end()) {
            lt->second.emplace_back(std::move(cont));
            return;
        }
        inflights[virtual_offset].emplace_back(cont);
        find_owning_receiver receiver(
            aux,
            node_cache,
            inflights,
            read_offset,
            virtual_offset,
            std::move(machine));
        detail::initiate_async_read_update(
            *aux.io, std::move(receiver), receiver.bytes_to_read);
    }
}

// Use a hashtable for inflight requests, it maps a file offset to a list of
// requests. If a read request exists in the hash table, simply append to an
// existing inflight read, Otherwise, send a read request and put itself on the
// map
void find_notify_fiber_future(
    UpdateAuxImpl &aux, inflight_map_t &inflights,
    threadsafe_boost_fibers_promise<find_cursor_result_type> &promise,
    NodeCursor root, NibblesView const key)
{
    if (!root.is_valid()) {
        promise.set_value(
            {NodeCursor{}, find_result::root_node_is_null_failure});
        return;
    }
    unsigned prefix_index = 0;
    unsigned node_prefix_index = root.prefix_index;
    Node *node = root.node;
    auto &machine = root.machine;
    for (; node_prefix_index < node->path_nibbles_len();
         ++node_prefix_index, ++prefix_index) {
        if (prefix_index >= key.nibble_size()) {
            promise.set_value(
                {NodeCursor{std::move(machine), *node, node_prefix_index},
                 find_result::key_ends_earlier_than_node_failure});
            return;
        }
        auto const nibble = node->path_nibble_view().get(node_prefix_index);
        machine->down(nibble);
        if (key.get(prefix_index) != nibble) {
            promise.set_value(
                {NodeCursor{std::move(machine), *node, node_prefix_index},
                 find_result::key_mismatch_failure});
            return;
        }
    }
    if (prefix_index == key.nibble_size()) {
        promise.set_value(
            {NodeCursor{std::move(machine), *node, node_prefix_index},
             find_result::success});
        return;
    }
    MONAD_ASSERT(prefix_index < key.nibble_size());
    MONAD_ASSERT(node_prefix_index == node->path_nibbles_len());
    if (unsigned char const branch = key.get(prefix_index);
        node->mask & (1u << branch)) {
        machine->down(branch);
        MONAD_DEBUG_ASSERT(
            prefix_index < std::numeric_limits<unsigned char>::max());
        auto const next_key =
            key.substr(static_cast<unsigned char>(prefix_index) + 1u);
        auto const child_index = node->to_child_index(branch);
        auto *const next_node = node->next(child_index);
        if (aux.is_on_disk()) { // check for auto-expire
            chunk_offset_t const offset = node->fnext(child_index);
            auto const list_type =
                aux.db_metadata()->at(offset.id)->which_list();
            if (!machine->auto_expire()) {
                MONAD_ASSERT(
                    list_type != chunk_list::expire &&
                    list_type != chunk_list::free);
            }
            else if (MONAD_UNLIKELY(
                         list_type != chunk_list::expire ||
                         aux.physical_to_virtual(offset) <
                             aux.get_min_virtual_expire_offset_metadata())) {
                promise.set_value(
                    {NodeCursor{},
                     find_result::node_is_pruned_by_auto_expiration});
                return;
            }
            if (next_node == nullptr) { // to load next node from disk
                if (aux.io->owning_thread_id() != get_tl_tid()) {
                    promise.set_value(
                        {NodeCursor{
                             std::move(machine), *node, node_prefix_index},
                         find_result::need_to_continue_in_io_thread});
                    return;
                }
                auto cont =
                    [&aux,
                     &inflights,
                     &promise,
                     next_key,
                     node_prefix_index = node->next_relpath_start_index()](
                        Node &node, std::unique_ptr<StateMachine> machine)
                    -> result<void> {
                    find_notify_fiber_future(
                        aux,
                        inflights,
                        promise,
                        NodeCursor{std::move(machine), node, node_prefix_index},
                        next_key);
                    return success();
                };
                if (auto lt = inflights.find(offset); lt != inflights.end()) {
                    lt->second.emplace_back(cont);
                    return;
                }
                inflights[offset].emplace_back(cont);
                find_receiver receiver(
                    aux, inflights, node, branch, std::move(machine));
                detail::initiate_async_read_update(
                    *aux.io, std::move(receiver), receiver.bytes_to_read);
                return;
            }
        }
        find_notify_fiber_future(
            aux,
            inflights,
            promise,
            {std::move(machine), *next_node, node->next_relpath_start_index()},
            next_key);
    }
    else {
        promise.set_value(
            {NodeCursor{std::move(machine), *node, node_prefix_index},
             find_result::branch_not_exist_failure});
    }
}

// Look up from node_cache first, issue read if miss and not in inflight
// Upon read completion, deserialize node and add to node_cache
void find_owning_notify_fiber_future(
    UpdateAuxImpl &aux, NodeCache &node_cache, inflight_map_owning_t &inflights,
    threadsafe_boost_fibers_promise<find_owning_cursor_result_type> &promise,
    OwningNodeCursor &start, NibblesView const key, uint64_t const version)
{
    MONAD_ASSERT(aux.is_on_disk());
    if (!aux.version_is_valid_ondisk(version)) {
        promise.set_value({start, find_result::version_no_longer_exist});
        return;
    }
    if (!start.is_valid()) {
        promise.set_value(
            {OwningNodeCursor{}, find_result::root_node_is_null_failure});
        return;
    }
    unsigned prefix_index = 0;
    unsigned node_prefix_index = start.prefix_index;
    auto node = start.node;
    auto &machine = start.machine;
    for (; node_prefix_index < node->path_nibbles_len();
         ++node_prefix_index, ++prefix_index) {
        if (prefix_index >= key.nibble_size()) {
            promise.set_value(
                {OwningNodeCursor{std::move(machine), node, node_prefix_index},
                 find_result::key_ends_earlier_than_node_failure});
            return;
        }
        auto const nibble = node->path_nibble_view().get(node_prefix_index);
        machine->down(nibble);
        if (key.get(prefix_index) != nibble) {
            promise.set_value(
                {OwningNodeCursor{std::move(machine), node, node_prefix_index},
                 find_result::key_mismatch_failure});
            return;
        }
    }
    if (prefix_index == key.nibble_size()) {
        promise.set_value(
            {OwningNodeCursor{std::move(machine), node, node_prefix_index},
             find_result::success});
        return;
    }
    MONAD_ASSERT(prefix_index < key.nibble_size());
    MONAD_ASSERT(node_prefix_index == node->path_nibbles_len());
    if (unsigned char const branch = key.get(prefix_index);
        node->mask & (1u << branch)) {
        machine->down(branch);
        MONAD_DEBUG_ASSERT(
            prefix_index < std::numeric_limits<unsigned char>::max());
        auto const next_key =
            key.substr(static_cast<unsigned char>(prefix_index) + 1u);
        auto const child_index = node->to_child_index(branch);
        auto const next_node_offset = node->fnext(child_index);
        auto const next_virtual_offset =
            aux.physical_to_virtual(next_node_offset);
        // version validity check must be after the virtual offset translation
        if (!aux.version_is_valid_ondisk(version) ||
            next_virtual_offset == INVALID_VIRTUAL_OFFSET) {
            promise.set_value({start, find_result::version_no_longer_exist});
            return;
        }
        // verify the offset to read is still valid and has not been reused
        auto const list_type =
            aux.db_metadata()->at(next_node_offset.id)->which_list();
        if (!machine->auto_expire()) {
            MONAD_ASSERT(
                list_type != chunk_list::expire &&
                list_type != chunk_list::free);
        }
        else if (MONAD_UNLIKELY(
                     list_type != chunk_list::expire ||
                     next_virtual_offset <
                         aux.get_min_virtual_expire_offset_metadata())) {
            promise.set_value(
                {OwningNodeCursor{},
                 find_result::node_is_pruned_by_auto_expiration});
            return;
        }
        NodeCache::ConstAccessor acc;
        if (node_cache.find(acc, next_virtual_offset)) {
            OwningNodeCursor next_cursor{
                std::move(machine),
                acc->second->val,
                node->next_relpath_start_index()};
            find_owning_notify_fiber_future(
                aux,
                node_cache,
                inflights,
                promise,
                next_cursor,
                next_key,
                version);
            return;
        }
        unsigned const next_node_prefix_index =
            node->next_relpath_start_index();
        auto cont =
            [&aux,
             &node_cache,
             &inflights,
             &promise,
             next_key,
             next_node_prefix_index, // must be captured here to because the
                                     // same node in inflights can be used in
                                     // continuations for different versions
                                     // where the starting prefix index can be
                                     // different
             version](
                std::shared_ptr<Node> &node,
                std::unique_ptr<StateMachine>
                    machine) -> result<void> {
            if (node == nullptr) {
                promise.set_value(
                    {OwningNodeCursor{}, find_result::version_no_longer_exist});
                return success();
            }
            MONAD_ASSERT(machine != nullptr);
            OwningNodeCursor node_cursor{
                std::move(machine), node, next_node_prefix_index};
            find_owning_notify_fiber_future(
                aux,
                node_cache,
                inflights,
                promise,
                node_cursor,
                next_key,
                version);
            return success();
        };
        async_read_with_continuation(
            aux,
            node_cache,
            inflights,
            promise,
            cont,
            next_node_offset,
            next_virtual_offset,
            std::move(machine));
    }
    else {
        promise.set_value(
            {OwningNodeCursor{std::move(machine), node, node_prefix_index},
             find_result::branch_not_exist_failure});
    }
}

void load_root_notify_fiber_future(
    UpdateAuxImpl &aux, NodeCache &node_cache, inflight_map_owning_t &inflights,
    threadsafe_boost_fibers_promise<find_owning_cursor_result_type> &promise,
    uint64_t const version, std::unique_ptr<StateMachine> machine)
{
    auto const root_offset = aux.get_root_offset_at_version(version);
    auto const root_virtual_offset = aux.physical_to_virtual(root_offset);
    // version validity check must be after the virtual offset translation
    if (!aux.version_is_valid_ondisk(version) ||
        root_virtual_offset == INVALID_VIRTUAL_OFFSET) {
        promise.set_value(
            {OwningNodeCursor{}, find_result::version_no_longer_exist});
        return;
    }
    NodeCache::ConstAccessor acc;
    if (node_cache.find(acc, root_virtual_offset)) {
        auto &root = acc->second->val;
        MONAD_ASSERT(root != nullptr);
        promise.set_value(
            {OwningNodeCursor{std::move(machine), root}, find_result::success});
        return;
    }
    auto cont =
        [&promise](
            std::shared_ptr<Node> &node, std::unique_ptr<StateMachine> machine)
        -> result<void> {
        if (node) {
            promise.set_value(
                {OwningNodeCursor{std::move(machine), node},
                 find_result::success});
        }
        else {
            promise.set_value(
                {OwningNodeCursor{}, find_result::version_no_longer_exist});
        }
        return success();
    };
    async_read_with_continuation(
        aux,
        node_cache,
        inflights,
        promise,
        cont,
        root_offset,
        root_virtual_offset,
        std::move(machine));
}

MONAD_MPT_NAMESPACE_END
