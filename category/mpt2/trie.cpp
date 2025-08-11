#include <category/core/byte_string.hpp>
#include <category/mpt2/child_data.hpp>
#include <category/mpt2/nibbles_view.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/request.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/update.hpp>
#include <category/mpt2/util.hpp>

#include <cstdint>

MONAD_MPT2_NAMESPACE_BEGIN

struct PendingNode;

void create_new_trie(
    UpdateAux &aux, StateMachine &sm, int64_t &parent_version, ChildData &entry,
    UpdateList &&updates, unsigned prefix_index = 0);

void create_new_trie_from_requests(
    UpdateAux &, StateMachine &, ChildData &entry, int64_t &parent_version,
    Requests &, NibblesView path, unsigned prefix_index,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void upsert_recursive(
    UpdateAux &, StateMachine &, PendingNode &parent, ChildData &, Node &old,
    UpdateList &&, unsigned prefix_index = 0, unsigned old_prefix_index = 0);

void update_value_and_subtrie(
    UpdateAux &, StateMachine &, PendingNode &parent, ChildData &entry,
    Node &old, NibblesView path, Update &);

void dispatch_updates_impl(
    UpdateAux &, StateMachine &, PendingNode &parent, ChildData &entry,
    Node &old, Requests &, unsigned prefix_index, NibblesView path,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void mismatch_handler(
    UpdateAux &, StateMachine &, PendingNode &parent, ChildData &entry,
    Node &old, Requests &, NibblesView path, unsigned old_prefix_index,
    unsigned prefix_index);

Node::UniquePtr write_children_create_node(
    UpdateAux &, StateMachine &, uint16_t orig_mask, uint16_t mask,
    std::span<ChildData> children, NibblesView path,
    std::optional<byte_string_view> opt_leaf_data, int64_t version);

void create_node_compute_data(
    UpdateAux &, StateMachine &, PendingNode &parent, ChildData &entry,
    PendingNode &current);

struct PendingNode
{
    uint16_t mask{0};
    uint16_t orig_mask{0};
    std::vector<ChildData> children{};
    Nibbles path{};
    std::optional<byte_string_view> opt_leaf_data{std::nullopt};
    int64_t version{0};

    PendingNode(
        uint16_t const orig_mask, NibblesView const path = {},
        std::optional<byte_string_view> const opt_leaf_data = std::nullopt,
        int64_t const version = 0)
        : mask(orig_mask)
        , orig_mask(orig_mask)
        , children(static_cast<unsigned>(std::popcount(orig_mask)))
        , path(path)
        , opt_leaf_data(opt_leaf_data)
        , version(version)
    {
    }
};

static_assert(sizeof(PendingNode) == 80);
static_assert(alignof(PendingNode) == 8);

// should it return an offset? and take an offset?
chunk_offset_t upsert(
    UpdateAux &aux, uint64_t const version, StateMachine &sm,
    chunk_offset_t const old_offset, UpdateList &&updates)
{
    Node *const old = aux.parse_node(old_offset);
    PendingNode sentinel{1}; // single child
    ChildData &entry = sentinel.children[0];
    entry.branch = 0;
    if (old) {
        if (updates.empty()) {
            auto const old_path = old->path_nibble_view();
            auto const old_path_nibbles_len = old_path.nibble_size();
            for (unsigned n = 0; n < old_path_nibbles_len; ++n) {
                sm.down(old_path.get(n));
            }
            // simply dispatch empty update and potentially do compaction
            Requests requests;
            dispatch_updates_impl(
                aux,
                sm,
                sentinel,
                entry,
                *old,
                requests,
                old_path_nibbles_len,
                old_path,
                old->opt_value(),
                old->version);
            sm.up(old_path_nibbles_len);
        }
        else {
            upsert_recursive(
                aux, sm, sentinel, entry, *old, std::move(updates));
        }
    }
    else {
        create_new_trie(aux, sm, sentinel.version, entry, std::move(updates));
    }
    // this function is not responsible to update the version ring buffer in
    // db_metadata, will do it on a higher layer
    // The update of root offset in the version ring buffer is atomic and
    // guarantee the atomicity of db transaction
    return entry.node ? aux.write_node_to_disk(*entry.node, version)
                      : INVALID_OFFSET;
}

std::pair<compact_virtual_chunk_offset_t, compact_virtual_chunk_offset_t>
calc_min_offsets(
    Node const &node, virtual_chunk_offset_t const node_virtual_offset)
{
    auto fast_ret = INVALID_COMPACT_VIRTUAL_OFFSET;
    auto slow_ret = INVALID_COMPACT_VIRTUAL_OFFSET;
    if (node_virtual_offset != INVALID_VIRTUAL_OFFSET) {
        auto const truncated_offset =
            compact_virtual_chunk_offset_t{node_virtual_offset};
        if (node_virtual_offset.in_fast_list()) {
            fast_ret = truncated_offset;
        }
        else {
            slow_ret = truncated_offset;
        }
    }
    for (unsigned i = 0; i < node.number_of_children(); ++i) {
        fast_ret = std::min(fast_ret, node.min_offset_fast(i));
        slow_ret = std::min(slow_ret, node.min_offset_slow(i));
    }
    // if ret is valid
    if (fast_ret != INVALID_COMPACT_VIRTUAL_OFFSET) {
        MONAD_ASSERT(fast_ret < (1u << 31));
    }
    if (slow_ret != INVALID_COMPACT_VIRTUAL_OFFSET) {
        MONAD_ASSERT(slow_ret < (1u << 31));
    }
    return {fast_ret, slow_ret};
}

Node::UniquePtr write_children_create_node(
    UpdateAux &aux, StateMachine &sm, uint16_t const orig_mask,
    uint16_t const mask, std::span<ChildData> children, NibblesView const path,
    std::optional<byte_string_view> const opt_leaf_data, int64_t const version)
{
    auto const number_of_children = static_cast<unsigned>(std::popcount(mask));
    if (number_of_children == 0) {
        return opt_leaf_data.has_value()
                   ? make_node(0, {}, path, opt_leaf_data.value(), {}, version)
                   : nullptr;
    }
    else if (number_of_children == 1 && !opt_leaf_data.has_value()) {
        // coalesce single child node with parent path
        auto const j = bitmask_index(
            orig_mask, static_cast<unsigned>(std::countr_zero(mask)));
        MONAD_DEBUG_ASSERT(children[j].node);
        auto const node = std::move(children[j].node);
        /* Note: there's a potential superfluous extension hash recomputation
        when node coaleases upon erases, because we compute node hash when path
        is not yet the final form. There's not yet a good way to avoid this
        unless we delay all the compute() after all child branches finish
        creating nodes and return in the recursion */
        return make_node(
            *node,
            concat(path, children[j].branch, node->path_nibble_view()),
            node->opt_value(),
            version);
    }
    MONAD_DEBUG_ASSERT(
        number_of_children > 1 ||
        (number_of_children == 1 && opt_leaf_data.has_value()));
    // write all children to disk
    for (auto &child : children) {
        if (child.need_write_to_disk()) {
            // write updated node or node to be compacted to disk
            // won't duplicate write of unchanged old child
            child.offset = aux.write_node_to_disk(
                *child.node, true); // end of child.node lifetime
            auto const child_virtual_offset =
                aux.physical_to_virtual(child.offset);
            std::tie(child.min_offset_fast, child.min_offset_slow) =
                calc_min_offsets(*child.node, child_virtual_offset);
        }
    }
    return create_node_with_children(
        sm.get_compute(), mask, children, path, opt_leaf_data, version);
}

void create_node_compute_data(
    UpdateAux &aux, StateMachine &sm, PendingNode &parent, ChildData &entry,
    PendingNode &current)
{
    auto node = write_children_create_node(
        aux,
        sm,
        current.orig_mask,
        current.mask,
        current.children,
        current.path,
        current.opt_leaf_data,
        current.version);
    MONAD_DEBUG_ASSERT(entry.branch < 16);
    if (node) {
        entry.finalize(std::move(node), sm.get_compute());
    }
    else { // the branch represented by `current` is fully erased
        parent.mask &=
            static_cast<uint16_t>(~(static_cast<uint16_t>(1u << entry.branch)));
        entry.erase();
    }
}

void upsert_recursive(
    UpdateAux &aux, StateMachine &sm, PendingNode &parent, ChildData &entry,
    Node &old, UpdateList &&updates, unsigned prefix_index,
    unsigned old_prefix_index)
{
    MONAD_ASSERT(!updates.empty());
    // Variable-length tables support only a one-time insert; no deletions or
    // further updates are allowed.
    MONAD_ASSERT(
        !sm.is_variable_length(),
        "Invalid update detected: current implementation does not "
        "support updating variable-length tables");
    MONAD_ASSERT(old_prefix_index != INVALID_PATH_INDEX);
    auto const old_prefix_index_start = old_prefix_index;
    auto const prefix_index_start = prefix_index;
    Requests requests;
    while (true) {
        NibblesView path = old.path_nibble_view().substr(
            old_prefix_index_start, old_prefix_index - old_prefix_index_start);
        if (updates.size() == 1 &&
            prefix_index == updates.front().key.nibble_size()) {
            auto &update = updates.front();
            MONAD_ASSERT(old.path_nibbles_len() == old_prefix_index);
            MONAD_ASSERT(old.has_value());
            update_value_and_subtrie(aux, sm, parent, entry, old, path, update);
            break;
        }
        unsigned const number_of_sublists = requests.split_into_sublists(
            std::move(updates), prefix_index); // NOLINT
        if (old_prefix_index == old.path_nibbles_len()) {
            MONAD_ASSERT(
                !requests.opt_leaf.has_value(),
                "Invalid update detected: cannot apply variable-length "
                "updates to a fixed-length table in the database");
            dispatch_updates_impl(
                aux,
                sm,
                parent,
                entry,
                old,
                requests,
                prefix_index,
                path,
                old.opt_value(),
                old.version);
            break;
        }
        if (auto old_nibble = old.path_nibble_view().get(old_prefix_index);
            number_of_sublists == 1 &&
            requests.get_first_branch() == old_nibble) {
            MONAD_DEBUG_ASSERT(requests.opt_leaf == std::nullopt);
            updates = std::move(requests)[old_nibble];
            sm.down(old_nibble);
            ++prefix_index;
            ++old_prefix_index;
            continue;
        }
        // meet a mismatch or split, not till the end of old path
        mismatch_handler(
            aux,
            sm,
            parent,
            entry,
            old,
            requests,
            path,
            old_prefix_index,
            prefix_index);
        break;
    }
    if (prefix_index_start != prefix_index) {
        sm.up(prefix_index - prefix_index_start);
    }
}

void update_value_and_subtrie(
    UpdateAux &aux, StateMachine &sm, PendingNode &parent, ChildData &entry,
    Node &old, NibblesView const path, Update &update)
{
    if (update.is_deletion()) {
        parent.mask &= static_cast<uint16_t>(~(1u << entry.branch));
        entry.erase();
        return;
    }
    // No need to check next is empty or not, following branches will handle it
    Requests requests;
    requests.split_into_sublists(std::move(update.next), 0);
    MONAD_ASSERT(requests.opt_leaf == std::nullopt);
    if (update.incarnation) {
        // handles empty requests sublist too
        create_new_trie_from_requests(
            aux,
            sm,
            entry,
            parent.version,
            requests,
            path,
            0,
            update.value,
            update.version);
    }
    else {
        auto const opt_leaf =
            update.value.has_value() ? update.value : old.opt_value();
        MONAD_ASSERT(update.version >= old.version);
        dispatch_updates_impl(
            aux,
            sm,
            parent,
            entry,
            old,
            requests,
            0,
            path,
            opt_leaf,
            update.version);
    }
    return;
}

/* dispatch updates at the end of old node's path. old node may have leaf data,
 * and there might be update to the leaf value. */
void dispatch_updates_impl(
    UpdateAux &aux, StateMachine &sm, PendingNode &parent, ChildData &entry,
    Node &old, Requests &requests, unsigned const prefix_index,
    NibblesView const path, std::optional<byte_string_view> const opt_leaf_data,
    int64_t const version)
{
    uint16_t const orig_mask = old.mask | requests.mask;
    PendingNode current{orig_mask, path, opt_leaf_data, version};
    auto &children = current.children;
    for (auto const [index, branch] : NodeChildrenRange(orig_mask)) {
        if ((1 << branch) & requests.mask) {
            children[index].branch = branch;
            sm.down(branch);
            if ((1 << branch) & old.mask) {
                upsert_recursive(
                    aux,
                    sm,
                    current,
                    children[index],
                    *aux.parse_node(old.fnext(old.to_child_index(branch))),
                    std::move(requests)[branch],
                    prefix_index + 1);
                sm.up(1);
            }
            else {
                create_new_trie(
                    aux,
                    sm,
                    current.version,
                    children[index],
                    std::move(requests)[branch],
                    prefix_index + 1);
                sm.up(1);
            }
        }
        else if ((1 << branch) & old.mask) {
            children[index].copy_old_child(old, branch);
            // TODO: compaction
        }
    }
    create_node_compute_data(aux, sm, parent, entry, current);
}

void mismatch_handler(
    UpdateAux &aux, StateMachine &sm, PendingNode &parent, ChildData &entry,
    Node &old, Requests &requests, NibblesView const path,
    unsigned const old_prefix_index, unsigned const prefix_index)
{
    MONAD_DEBUG_ASSERT(old.has_path());
    // Note: no leaf can be created at an existing non-leaf node
    MONAD_DEBUG_ASSERT(!requests.opt_leaf.has_value());
    unsigned char const old_nibble =
        old.path_nibble_view().get(old_prefix_index);
    uint16_t const orig_mask =
        static_cast<uint16_t>(1u << old_nibble | requests.mask);
    PendingNode current{orig_mask, path};
    auto &children = current.children;
    for (auto const [index, branch] : NodeChildrenRange(orig_mask)) {
        if ((1 << branch) & requests.mask) {
            children[index].branch = branch;
            sm.down(branch);
            if (branch == old_nibble) {
                upsert_recursive(
                    aux,
                    sm,
                    current,
                    children[index],
                    old,
                    std::move(requests)[branch],
                    prefix_index + 1,
                    old_prefix_index + 1);
            }
            else {
                create_new_trie(
                    aux,
                    sm,
                    current.version,
                    children[index],
                    std::move(requests)[branch],
                    prefix_index + 1);
            }
            sm.up(1);
        }
        else if (branch == old_nibble) {
            sm.down(old_nibble);
            // nexts[index] is a path-shortened old node, trim prefix
            NibblesView const path_suffix =
                old.path_nibble_view().substr(old_prefix_index + 1);
            for (auto i = 0u; i < path_suffix.nibble_size(); ++i) {
                sm.down(path_suffix.get(i));
            }
            auto &child = children[index];
            child.branch = branch;
            child.finalize(
                make_node(old, path_suffix, old.opt_value(), old.version),
                sm.get_compute());
            sm.up(path_suffix.nibble_size() + 1);
            // TODO: compaction
        }
    }
    create_node_compute_data(aux, sm, parent, entry, current);
}

void create_new_trie_from_requests(
    UpdateAux &aux, StateMachine &sm, ChildData &entry, int64_t &parent_version,
    Requests &requests, NibblesView const path, unsigned const prefix_index,
    std::optional<byte_string_view> const opt_leaf_data, int64_t version)
{
    // version will be updated bottom up
    uint16_t const mask = requests.mask;
    std::vector<ChildData> children(size_t(std::popcount(mask)));
    for (auto const [index, branch] : NodeChildrenRange(mask)) {
        children[index].branch = branch;
        sm.down(branch);
        create_new_trie(
            aux,
            sm,
            version,
            children[index],
            std::move(requests)[branch],
            prefix_index + 1);
        sm.up(1);
    }
    // can have empty children
    entry.finalize(
        write_children_create_node(
            aux, sm, mask, mask, children, path, opt_leaf_data, version),
        sm.get_compute());
    parent_version = std::max(parent_version, entry.node->version);

    // if (sm.auto_expire()) {
    //     MONAD_ASSERT(
    //         entry.subtrie_min_version >=
    //         aux.curr_upsert_auto_expire_version);
    // }
}

void create_new_trie(
    UpdateAux &aux, StateMachine &sm, int64_t &parent_version, ChildData &entry,
    UpdateList &&updates, unsigned prefix_index)
{
    if (updates.empty()) {
        return;
    }
    if (updates.size() == 1) {
        Update &update = updates.front();
        MONAD_DEBUG_ASSERT(update.value.has_value());
        auto const path = update.key.substr(prefix_index);
        for (auto i = 0u; i < path.nibble_size(); ++i) {
            sm.down(path.get(i));
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
        create_new_trie_from_requests(
            aux,
            sm,
            entry,
            parent_version,
            requests,
            path,
            0,
            update.value,
            update.version);
        if (path.nibble_size()) {
            sm.up(path.nibble_size());
        }
        return;
    }
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
    create_new_trie_from_requests(
        aux,
        sm,
        entry,
        parent_version,
        requests,
        requests.get_first_path().substr(
            prefix_index_start, prefix_index - prefix_index_start),
        prefix_index,
        requests.opt_leaf.and_then(&Update::value),
        requests.opt_leaf.has_value() ? requests.opt_leaf.value().version : 0);
    if (prefix_index_start != prefix_index) {
        sm.up(prefix_index - prefix_index_start);
    }
}

MONAD_MPT2_NAMESPACE_END
