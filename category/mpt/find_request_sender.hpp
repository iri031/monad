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

#pragma once

#include <category/async/concepts.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include "deserialize_node_from_receiver_result.hpp"

#include <cstdint>
#include <limits>

MONAD_MPT_NAMESPACE_BEGIN

struct inflight_node_hasher
{
    constexpr size_t operator()(
        std::pair<virtual_chunk_offset_t, CacheNode *> const &v) const noexcept
    {
        return virtual_chunk_offset_t_hasher{}(v.first) ^
               fnv1a_hash<CacheNode *>()(v.second);
    }
};

// Index in progress node ios by physical read offset and parent node pointer.
// Nodes in cache are implicitly owned by taking reference to the root node.
// Since result of io is shared between requests, they need to share the
// root node to ensure proper ownership. Because nodes in cache are unique,
// having a pointer to parent as key ensures requests share the same root node
// as well.
using AsyncInflightNodes = unordered_dense_map<
    std::pair<virtual_chunk_offset_t, CacheNode *>,
    std::vector<
        std::function<MONAD_ASYNC_NAMESPACE::result<void>(OwningNodeCursor)>>,
    inflight_node_hasher>;

template <class T>
concept return_type =
    std::same_as<T, byte_string> || std::same_as<T, std::shared_ptr<CacheNode>>;

/*! \brief Sender to perform the asynchronous finding of a node.
 */
template <return_type T = byte_string>
class find_request_sender
{
private:
    struct find_receiver;
    friend struct find_receiver;

    UpdateAuxImpl &aux_;
    NodeCache &node_cache_;
    OwningNodeCursor root_;
    NibblesView key_;
    AsyncInflightNodes &inflights_;
    std::optional<find_result_type<T>> res_{std::nullopt};
    bool tid_checked_{false};
    bool return_value_{true};

    MONAD_ASYNC_NAMESPACE::result<void> resume_(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
        OwningNodeCursor root)
    {
        root_ = root;
        MONAD_ASSERT(root_.is_valid());
        return (*this)(io_state);
    }

public:
    using result_type = MONAD_ASYNC_NAMESPACE::result<find_result_type<T>>;

    constexpr find_request_sender(
        UpdateAuxImpl &aux, NodeCache &node_cache,
        AsyncInflightNodes &inflights, OwningNodeCursor root,
        NibblesView const key, bool const return_value)
        : aux_(aux)
        , node_cache_(node_cache)
        , root_(root)
        , key_(key)
        , inflights_(inflights)
        , return_value_(return_value)
    {
        MONAD_ASSERT(root_.is_valid());
    }

    void reset(OwningNodeCursor root, NibblesView key)
    {
        root_ = root;
        key_ = key;
        MONAD_ASSERT(root_.is_valid());
        tid_checked_ = false;
    }

    MONAD_ASYNC_NAMESPACE::result<void>
    operator()(MONAD_ASYNC_NAMESPACE::erased_connected_operation *) noexcept;

    result_type completed(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
        MONAD_ASYNC_NAMESPACE::result<void> res) noexcept
    {
        BOOST_OUTCOME_TRY(std::move(res));
        MONAD_ASSERT(res_.has_value());
        return {std::move(*res_)};
    }
};

static_assert(sizeof(find_request_sender<byte_string>) == 120);
static_assert(alignof(find_request_sender<byte_string>) == 8);
static_assert(MONAD_ASYNC_NAMESPACE::sender<find_request_sender<byte_string>>);

static_assert(sizeof(find_request_sender<std::shared_ptr<CacheNode>>) == 104);
static_assert(alignof(find_request_sender<std::shared_ptr<CacheNode>>) == 8);
static_assert(MONAD_ASYNC_NAMESPACE::sender<
              find_request_sender<std::shared_ptr<CacheNode>>>);

// TODO: fix the version out of history range UB by version validation after
// each io
template <return_type T>
struct find_request_sender<T>::find_receiver
{
    static constexpr bool lifetime_managed_internally = true;

    find_request_sender *const sender;
    MONAD_ASYNC_NAMESPACE::erased_connected_operation *const io_state;

    chunk_offset_t rd_offset{0, 0}; // required for sender
    unsigned bytes_to_read; // required for sender too
    uint16_t buffer_off;
    unsigned const branch_index;
    unsigned const branch;

    constexpr find_receiver(
        find_request_sender *sender_,
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state_,
        unsigned char const branch)
        : sender(sender_)
        , io_state(io_state_)
        , branch_index(sender->root_.node->to_child_index(branch))
        , branch(branch)
    {
        MONAD_ASSERT(sender->root_.node->mask & (1u << branch));
        chunk_offset_t const offset = sender->root_.node->fnext(branch_index);
        auto const num_pages_to_load_node =
            node_disk_pages_spare_15{offset}.to_pages();
        bytes_to_read =
            static_cast<unsigned>(num_pages_to_load_node << DISK_PAGE_BITS);
        rd_offset = offset;
        auto const new_offset = round_down_align<DISK_PAGE_BITS>(offset.offset);
        MONAD_DEBUG_ASSERT(new_offset <= chunk_offset_t::max_offset);
        rd_offset.offset = new_offset & chunk_offset_t::max_offset;
        buffer_off = uint16_t(offset.offset - rd_offset.offset);
    }

    // notify a list of requests pending on this node
    template <class ResultType>
    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *, ResultType buffer_)
    {
        MONAD_ASSERT(buffer_);
        MONAD_ASSERT(sender->root_.is_valid());
        auto const next_offset = sender->root_.node->fnext(branch_index);
        auto const virt_offset = sender->aux_.physical_to_virtual(next_offset);
        std::shared_ptr<CacheNode> sp =
            detail::deserialize_node_from_receiver_result<CacheNode>(
                std::move(buffer_), buffer_off, io_state);
        auto cache_it = sender->node_cache_.insert(virt_offset, sp);
        auto *const list_node = &*cache_it->second;
        sender->root_.node->set_next(branch_index, list_node);
        auto key = std::pair(virt_offset, sender->root_.node.get());
        auto it = sender->inflights_.find(key);
        if (it != sender->inflights_.end()) {
            auto pendings = std::move(it->second);
            sender->inflights_.erase(it);
            for (auto &invoc : pendings) {
                MONAD_ASSERT(invoc(OwningNodeCursor{sp}));
            }
        }
    }
};

template <return_type T>
inline MONAD_ASYNC_NAMESPACE::result<void> find_request_sender<T>::operator()(
    MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state) noexcept
{
    /* This is slightly bold, we basically repeatedly self reenter the Sender's
    initiation function until we complete. It is legal and it is allowed,
    just a bit quirky is all.
    */
    using namespace MONAD_ASYNC_NAMESPACE;
    for (;;) {
        unsigned prefix_index = 0;
        unsigned node_prefix_index = root_.prefix_index;
        MONAD_ASSERT(root_.is_valid());
        auto node = root_.node.get();
        for (; node_prefix_index < node->path_nibbles_len();
             ++node_prefix_index, ++prefix_index) {
            if (prefix_index >= key_.nibble_size()) {
                res_ = {T{}, find_result::key_ends_earlier_than_node_failure};
                io_state->completed(success());
                return success();
            }
            if (key_.get(prefix_index) !=
                node->path_nibble_view().get(node_prefix_index)) {
                res_ = {T{}, find_result::key_mismatch_failure};
                io_state->completed(success());
                return success();
            }
        }
        if (prefix_index == key_.nibble_size()) {
            if constexpr (std::is_same_v<T, byte_string>) {
                res_ = {
                    byte_string{return_value_ ? node->value() : node->data()},
                    find_result::success};
            }
            else {
                res_ = {root_.node, find_result::success};
            }
            io_state->completed(success());
            return success();
        }
        MONAD_ASSERT(prefix_index < key_.nibble_size());
        if (unsigned char const branch = key_.get(prefix_index);
            node->mask & (1u << branch)) {
            MONAD_DEBUG_ASSERT(
                prefix_index < std::numeric_limits<unsigned char>::max());
            key_ = key_.substr(static_cast<unsigned char>(prefix_index) + 1u);
            auto const child_index = node->to_child_index(branch);
            NodeCache::ConstAccessor acc;
            auto *p = reinterpret_cast<NodeCache::list_node *>(
                node->next(child_index));
            auto const offset = node->fnext(child_index);
            virtual_chunk_offset_t const virt_offset =
                aux_.physical_to_virtual(offset);
            if (p != nullptr && p->key == virt_offset) {
                // found cache entry with the desired key
                root_ = {p->val};
                MONAD_ASSERT(root_.is_valid());
                continue;
            }
            if (node_cache_.find(acc, virt_offset)) {
                auto *const list_node = &*acc->second;
                node->set_next(child_index, list_node);
                // found in LRU - no IO necessary
                root_ = {list_node->val};
                MONAD_ASSERT(root_.is_valid());
                continue;
            }
            if (!tid_checked_) {
                MONAD_ASSERT(aux_.io != nullptr);
                if (aux_.io->owning_thread_id() != get_tl_tid()) {
                    res_ = {T{}, find_result::need_to_continue_in_io_thread};
                    return success();
                }
                tid_checked_ = true;
            }
            auto cont = [this,
                         io_state](OwningNodeCursor root) -> result<void> {
                return this->resume_(io_state, root);
            };
            auto offset_node = std::pair(virt_offset, node);
            if (auto lt = inflights_.find(offset_node);
                lt != inflights_.end()) {
                lt->second.emplace_back(cont);
                return success();
            }
            inflights_[offset_node].emplace_back(cont);
            find_receiver receiver(this, io_state, branch);
            detail::initiate_async_read_update(
                *aux_.io, std::move(receiver), receiver.bytes_to_read);
            return success();
        }
        else {
            res_ = {T{}, find_result::branch_not_exist_failure};
            io_state->completed(success());
            return success();
        }
    }
}

MONAD_MPT_NAMESPACE_END
