#include <category/core/byte_string.hpp>
#include <category/core/keccak.h>
#include <category/core/mem/allocators.hpp>
#include <category/core/unaligned.hpp>
#include <category/mpt2/child_data.hpp>
#include <category/mpt2/compute.hpp>
#include <category/mpt2/nibbles_view.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/util.hpp>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_MPT2_NAMESPACE_BEGIN

allocators::detail::type_raw_alloc_pair<
    std::allocator<Node>, Node::BytesAllocator>
Node::pool()
{
    static std::allocator<Node> a;
    static BytesAllocator b;
    return {a, b};
}

size_t Node::get_deallocate_count(Node *node)
{
    return node->get_allocate_size();
}

Node::Node(prevent_public_construction_tag) {}

Node::Node(
    prevent_public_construction_tag, uint16_t const mask,
    std::optional<byte_string_view> value, size_t const data_size,
    NibblesView const path, int64_t const version)
    : mask(mask)
    , path_nibble_index_end(path.end_nibble_)
    , value_len(static_cast<decltype(value_len)>(
          value.transform(&byte_string_view::size).value_or(0)))
    , version(version)
{
    MONAD_DEBUG_ASSERT(
        value.transform(&byte_string_view::size).value_or(0) <=
        std::numeric_limits<decltype(value_len)>::max());
    MONAD_DEBUG_ASSERT(path.begin_nibble_ <= path.end_nibble_);
    bitpacked.path_nibble_index_start = path.begin_nibble_;
    bitpacked.has_value = value.has_value();

    MONAD_ASSERT(data_size <= Node::max_data_len);
    bitpacked.data_len = static_cast<uint8_t>(data_size & Node::max_data_len);

    if (path.data_size()) {
        MONAD_DEBUG_ASSERT(path.data_);
        std::copy_n(path.data_, path.data_size(), path_data());
    }

    if (value_len) {
        std::copy_n(value.value().data(), value.value().size(), value_data());
    }
}

unsigned Node::to_child_index(unsigned const branch) const noexcept
{
    // convert the enabled i'th bit in a 16-bit mask into its corresponding
    // index location - index
    MONAD_DEBUG_ASSERT(mask & (1u << branch));
    return bitmask_index(mask, branch);
}

unsigned Node::number_of_children() const noexcept
{
    return static_cast<unsigned>(std::popcount(mask));
}

chunk_offset_t const Node::fnext(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return unaligned_load<chunk_offset_t>(
        fnext_data + index * sizeof(chunk_offset_t));
}

void Node::set_fnext(unsigned const index, chunk_offset_t const off) noexcept
{
    std::memcpy(
        fnext_data + index * sizeof(chunk_offset_t),
        &off,
        sizeof(chunk_offset_t));
}

unsigned char *Node::child_min_offset_fast_data() noexcept
{
    return fnext_data + number_of_children() * sizeof(file_offset_t);
}

unsigned char const *Node::child_min_offset_fast_data() const noexcept
{
    return fnext_data + number_of_children() * sizeof(file_offset_t);
}

compact_virtual_chunk_offset_t
Node::min_offset_fast(unsigned const index) const noexcept
{
    return unaligned_load<compact_virtual_chunk_offset_t>(
        child_min_offset_fast_data() +
        index * sizeof(compact_virtual_chunk_offset_t));
}

void Node::set_min_offset_fast(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    std::memcpy(
        child_min_offset_fast_data() +
            index * sizeof(compact_virtual_chunk_offset_t),
        &offset,
        sizeof(compact_virtual_chunk_offset_t));
}

unsigned char *Node::child_min_offset_slow_data() noexcept
{
    return child_min_offset_fast_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

unsigned char const *Node::child_min_offset_slow_data() const noexcept
{
    return child_min_offset_fast_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

compact_virtual_chunk_offset_t
Node::min_offset_slow(unsigned const index) const noexcept
{
    return unaligned_load<compact_virtual_chunk_offset_t>(
        child_min_offset_slow_data() +
        index * sizeof(compact_virtual_chunk_offset_t));
}

void Node::set_min_offset_slow(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    std::memcpy(
        child_min_offset_slow_data() +
            index * sizeof(compact_virtual_chunk_offset_t),
        &offset,
        sizeof(compact_virtual_chunk_offset_t));
}

unsigned char *Node::child_min_version_data() noexcept
{
    return child_min_offset_slow_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

unsigned char const *Node::child_min_version_data() const noexcept
{
    return child_min_offset_slow_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

int64_t Node::subtrie_min_version(unsigned const index) const noexcept
{
    return unaligned_load<int64_t>(
        child_min_version_data() + index * sizeof(int64_t));
}

void Node::set_subtrie_min_version(
    unsigned const index, int64_t const min_version) noexcept
{
    std::memcpy(
        child_min_version_data() + index * sizeof(int64_t),
        &min_version,
        sizeof(int64_t));
}

unsigned char *Node::child_off_data() noexcept
{
    return child_min_version_data() + number_of_children() * sizeof(int64_t);
}

unsigned char const *Node::child_off_data() const noexcept
{
    return child_min_version_data() + number_of_children() * sizeof(int64_t);
}

uint16_t Node::child_data_offset(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index <= number_of_children());
    if (index == 0) {
        return 0;
    }
    return unaligned_load<uint16_t>(
        child_off_data() + (index - 1) * sizeof(uint16_t));
}

unsigned Node::child_data_len(unsigned const index) const
{
    return child_data_offset(index + 1) - child_data_offset(index);
}

unsigned Node::child_data_len()
{
    return child_data_offset(number_of_children()) - child_data_offset(0);
}

unsigned char *Node::path_data() noexcept
{
    return child_off_data() + number_of_children() * sizeof(uint16_t);
}

unsigned char const *Node::path_data() const noexcept
{
    return child_off_data() + number_of_children() * sizeof(uint16_t);
}

unsigned Node::path_nibbles_len() const noexcept
{
    MONAD_DEBUG_ASSERT(
        bitpacked.path_nibble_index_start <= path_nibble_index_end);
    return path_nibble_index_end - bitpacked.path_nibble_index_start;
}

bool Node::has_path() const noexcept
{
    return path_nibbles_len() > 0;
}

unsigned Node::path_bytes() const noexcept
{
    return (path_nibble_index_end + 1) / 2;
}

NibblesView Node::path_nibble_view() const noexcept
{
    return NibblesView{
        bitpacked.path_nibble_index_start, path_nibble_index_end, path_data()};
}

unsigned Node::path_start_nibble() const noexcept
{
    return bitpacked.path_nibble_index_start;
}

unsigned char *Node::value_data() noexcept
{
    return path_data() + path_bytes();
}

unsigned char const *Node::value_data() const noexcept
{
    return path_data() + path_bytes();
}

bool Node::has_value() const noexcept
{
    return bitpacked.has_value;
}

byte_string_view Node::value() const noexcept
{
    MONAD_DEBUG_ASSERT(has_value());
    return {value_data(), value_len};
}

std::optional<byte_string_view> Node::opt_value() const noexcept
{
    if (has_value()) {
        return value();
    }
    return std::nullopt;
}

unsigned char *Node::data_data() noexcept
{
    return value_data() + value_len;
}

unsigned char const *Node::data_data() const noexcept
{
    return value_data() + value_len;
}

byte_string_view Node::data() const noexcept
{
    return {data_data(), bitpacked.data_len};
}

unsigned char *Node::child_data() noexcept
{
    return data_data() + bitpacked.data_len;
}

unsigned char const *Node::child_data() const noexcept
{
    return data_data() + bitpacked.data_len;
}

byte_string_view Node::child_data_view(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return byte_string_view{
        child_data() + child_data_offset(index),
        static_cast<size_t>(child_data_len(index))};
}

unsigned char *Node::child_data(unsigned const index) noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return child_data() + child_data_offset(index);
}

void Node::set_child_data(unsigned const index, byte_string_view data) noexcept
{
    // called after data_off array is calculated
    std::memcpy(child_data(index), data.data(), data.size());
}

uint32_t Node::get_allocate_size() const noexcept
{
    MONAD_DEBUG_ASSERT(child_data() >= (unsigned char *)this);
    return static_cast<uint32_t>(
        child_data() + child_data_offset(number_of_children()) -
        (unsigned char *)this);
}

uint32_t Node::get_disk_size() const noexcept
{
    MONAD_DEBUG_ASSERT(child_data() >= (unsigned char *)this);
    uint32_t const total_disk_size =
        get_allocate_size() + Node::disk_size_bytes;
    MONAD_DEBUG_ASSERT(total_disk_size <= Node::max_disk_size);
    return total_disk_size;
}

Node::UniquePtr make_node(
    Node &from, NibblesView const path,
    std::optional<byte_string_view> const value, int64_t const version)
{
    auto const value_size =
        value.transform(&byte_string_view::size).value_or(0);
    auto node = Node::make(
        calculate_node_size(
            from.number_of_children(),
            from.child_data_len(),
            value_size,
            path.data_size(),
            from.data().size()),
        from.mask,
        value,
        from.data().size(),
        path,
        version);

    // fnext, min_count, child_data_offset
    std::copy_n(
        (byte_string::pointer)&from.fnext_data,
        from.path_data() - (byte_string::pointer)&from.fnext_data,
        (byte_string::pointer)&node->fnext_data);

    // copy data and child data
    std::copy_n(
        from.data_data(),
        from.data().size() + from.child_data_len(),
        node->data_data());

    return node;
}

Node::UniquePtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    size_t const data_size, int64_t const version)
{
    MONAD_DEBUG_ASSERT(data_size <= KECCAK256_SIZE);
    if (value.has_value()) {
        MONAD_DEBUG_ASSERT(
            value->size() <=
            std::numeric_limits<decltype(Node::value_len)>::max());
    }
    for (size_t i = 0; i < 16; ++i) {
        MONAD_DEBUG_ASSERT(
            !std::ranges::contains(children, i, &ChildData::branch) ||
            (mask & (1u << i)));
    }

    auto const number_of_children = static_cast<size_t>(std::popcount(mask));
    std::vector<uint16_t> child_data_offsets;
    child_data_offsets.reserve(children.size());
    uint16_t total_child_data_size = 0;
    for (auto const &child : children) {
        if (child.is_valid()) {
            total_child_data_size += child.data_size;
            child_data_offsets.push_back(total_child_data_size);
        }
    }

    auto node = Node::make(
        calculate_node_size(
            number_of_children,
            total_child_data_size,
            value.transform(&byte_string_view::size).value_or(0),
            path.data_size(),
            data_size),
        mask,
        value,
        data_size,
        path,
        version);

    std::copy_n(
        (byte_string_view::pointer)child_data_offsets.data(),
        child_data_offsets.size() * sizeof(uint16_t),
        node->child_off_data());

    for (unsigned index = 0; auto &child : children) {
        if (child.is_valid()) {
            node->set_fnext(index, child.offset);
            node->set_min_offset_fast(index, child.min_offset_fast);
            node->set_min_offset_slow(index, child.min_offset_slow);
            node->set_subtrie_min_version(index, child.subtrie_min_version);
            node->set_child_data(index, {child.data, child.data_size});
            ++index;
        }
    }

    return node;
}

Node::UniquePtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    byte_string_view const data, int64_t const version)
{
    auto node = make_node(mask, children, path, value, data.size(), version);
    std::copy_n(data.data(), data.size(), node->data_data());
    return node;
}

// all children's offset are set before creating parent
// create node with at least one child
Node::UniquePtr create_node_with_children(
    Compute &comp, uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    int64_t const version)
{
    MONAD_ASSERT(mask);
    auto const data_size = comp.compute_len(children, mask, path, value);
    auto node = make_node(mask, children, path, value, data_size, version);
    MONAD_DEBUG_ASSERT(node);
    if (data_size) {
        comp.compute_branch(node->data_data(), node.get());
    }
    return node;
}

void serialize_node(unsigned char *write_pos, Node const &node)
{
    // write disk_size then node content
    uint32_t const disk_size = node.get_disk_size();
    MONAD_ASSERT(disk_size > 0 && disk_size <= Node::max_disk_size);
    memcpy(write_pos, (unsigned char *)&disk_size, Node::disk_size_bytes);
    write_pos += Node::disk_size_bytes;
    std::memcpy(
        write_pos, (unsigned char *)&node, disk_size - Node::disk_size_bytes);
}

// TODO: maybe pass in storage pool and verify the next_offset is within chunk
// range and valid, that would require it being moved to trie.hpp
Node *parse_node(unsigned char const *read_pos)
{
    // read node directly from mmap
    // TODO: prefetch
    auto const disk_size = unaligned_load<uint32_t>(read_pos);
    MONAD_ASSERT_PRINTF(
        disk_size <= Node::max_disk_size,
        "deserialized node disk size is %u",
        disk_size);
    read_pos += Node::disk_size_bytes;

    auto *const node = (Node *)read_pos;
    MONAD_ASSERT_PRINTF(
        disk_size == node->get_disk_size(),
        "Mismatched on disk node size: preceeding disk_size %u and "
        "node->get_disk_size() %u",
        disk_size,
        node->get_disk_size());
    return node;
}

Node::UniquePtr copy_node(Node const &node)
{
    auto new_node = Node::make(node.get_allocate_size());
    std::memcpy(
        (void *)new_node.get(), (void *)&node, node.get_allocate_size());
    return new_node;
}

MONAD_MPT2_NAMESPACE_END
