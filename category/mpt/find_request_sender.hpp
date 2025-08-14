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
    constexpr size_t
    operator()(std::pair<chunk_offset_t, Node *> const &v) const noexcept
    {
        return chunk_offset_t_hasher{}(v.first) ^
               fnv1a_hash<Node *>()(v.second);
    }
};

// Index in progress node ios by physical read offset and parent node pointer.
// Nodes in cache are implicitly owned by taking reference to the root node.
// Since result of io is shared between requests, they need to share the
// root node to ensure proper ownership. Because nodes in cache are unique,
// having a pointer to parent as key ensures requests share the same root node
// as well.
using inflight_node_t = unordered_dense_map<
    std::pair<chunk_offset_t, Node *>,
    std::vector<std::function<MONAD_ASYNC_NAMESPACE::result<void>(
        Node &, std::shared_ptr<Node>)>>,
    inflight_node_hasher>;

template <class T>
concept return_type =
    std::same_as<T, byte_string> || std::same_as<T, Node::UniquePtr>;

/*! \brief Sender to perform the asynchronous finding of a node.
 */
template <return_type T = byte_string>
class find_request_sender
{
private:
    struct find_receiver;
    friend struct find_receiver;

    UpdateAuxImpl &aux_;
    NodeCursor root_;
    NibblesView key_;
    inflight_node_t &inflights_;
    std::optional<find_result_type<T>> res_{std::nullopt};
    bool tid_checked_{false};
    bool return_value_{true};
    uint8_t const cached_levels_{5};
    uint8_t curr_level_{0};
    std::shared_ptr<Node> subtrie_with_sender_lifetime_{nullptr};

    MONAD_ASYNC_NAMESPACE::result<void> resume_(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
        NodeCursor root)
    {
        root_ = root;
        MONAD_ASSERT(root_.is_valid());
        return (*this)(io_state);
    }

public:
    using result_type = MONAD_ASYNC_NAMESPACE::result<find_result_type<T>>;

    constexpr find_request_sender(
        UpdateAuxImpl &aux, inflight_node_t &inflights, NodeCursor const root,
        NibblesView const key, bool const return_value,
        uint8_t const cached_levels)
        : aux_(aux)
        , root_(root)
        , key_(key)
        , inflights_(inflights)
        , return_value_(return_value)
        , cached_levels_(cached_levels)
    {
        MONAD_ASSERT(root_.is_valid());
    }

    void reset(NodeCursor root, NibblesView key)
    {
        root_ = root;
        key_ = key;
        curr_level_ = 0;
        subtrie_with_sender_lifetime_ = nullptr;
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

static_assert(sizeof(find_request_sender<Node::UniquePtr>) == 96);
static_assert(alignof(find_request_sender<Node::UniquePtr>) == 8);
static_assert(
    MONAD_ASYNC_NAMESPACE::sender<find_request_sender<Node::UniquePtr>>);

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

    constexpr find_receiver(
        find_request_sender *sender_,
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state_,
        unsigned char const branch)
        : sender(sender_)
        , io_state(io_state_)
        , branch_index(sender->root_.node->to_child_index(branch))
    {
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
        auto *node = sender->root_.node->next(branch_index);
        if (node == nullptr) {
            auto node_ptr = detail::deserialize_node_from_receiver_result(
                std::move(buffer_), buffer_off, io_state);
            node = node_ptr.get();
            /* Nodes that are within cached level shares the same lifetime as
             the root node of current version.
             Starting from cached_level, the lifetime of the node is refcounted,
             and all nodes that are visited below this level will remain alive
             as long as the pending `find_request_sender`s are */
            if (sender->curr_level_ > sender->cached_levels_ &&
                sender->subtrie_with_sender_lifetime_ == nullptr) {
                sender->subtrie_with_sender_lifetime_ = std::move(node_ptr);
            }
            else {
                sender->root_.node->set_next(branch_index, std::move(node_ptr));
            }
        }
        auto it =
            sender->inflights_.find(std::pair(next_offset, sender->root_.node));
        if (it != sender->inflights_.end()) {
            auto pendings = std::move(it->second);
            sender->inflights_.erase(it);
            auto subtrie_with_sender_lifetime_ =
                sender->subtrie_with_sender_lifetime_;
            for (auto &invoc : pendings) {
                MONAD_ASSERT(invoc(*node, subtrie_with_sender_lifetime_));
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
        Node *node = root_.node;
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
                res_ = {copy_node(node), find_result::success};
            }
            io_state->completed(success());
            return success();
        }
        MONAD_ASSERT(prefix_index < key_.nibble_size());
        MONAD_ASSERT(node_prefix_index == node->path_nibbles_len());
        if (unsigned char const branch = key_.get(prefix_index);
            node->mask & (1u << branch)) {
            MONAD_DEBUG_ASSERT(
                prefix_index < std::numeric_limits<unsigned char>::max());
            key_ = key_.substr(static_cast<unsigned char>(prefix_index) + 1u);
            auto const child_index = node->to_child_index(branch);
            ++this->curr_level_;
            if (node->next(child_index) != nullptr) {
                root_ = NodeCursor{
                    *node->next(child_index), node->next_relpath_start_index()};
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
            chunk_offset_t const offset = node->fnext(child_index);
            // `node_prefix_index` must be captured here to because the same
            // node in inflights can be used in continuations for different
            // versions where the starting prefix index can be different
            auto cont = [this,
                         io_state,
                         node_prefix_index = node->next_relpath_start_index()](
                            Node &root,
                            std::shared_ptr<Node>
                                subtrie_with_sender_lifetime_) -> result<void> {
                this->subtrie_with_sender_lifetime_ =
                    subtrie_with_sender_lifetime_;
                return this->resume_(
                    io_state, NodeCursor{root, node_prefix_index});
            };
            auto offset_node = std::pair(offset, node);
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
