#pragma once

#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/mem/allocators.hpp>
#include <category/mpt/detail/unsigned_20.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/util.hpp>
#include <category/mpt2/config.hpp>

#include <cstdint>
#include <optional>

MONAD_MPT2_NAMESPACE_BEGIN

using chunk_offset_t = MONAD_ASYNC_NAMESPACE::chunk_offset_t;
using file_offset_t = MONAD_ASYNC_NAMESPACE::file_offset_t;
using compact_virtual_chunk_offset_t =
    MONAD_MPT_NAMESPACE::compact_virtual_chunk_offset_t;
using NibblesView = MONAD_MPT_NAMESPACE::NibblesView;

/*
TODO:
- We need to expand virtual offset addressable space to more than 256Tb,
meaning that the compact_virtual_offset array in Node layout has to be expanded
to more bytes
*/

class Node
{
    struct prevent_public_construction_tag
    {
    };

public:
    static constexpr size_t max_number_of_children = 16;
    static constexpr uint8_t max_data_len = (1U << 6) - 1;
    static constexpr size_t max_disk_size =
        256 * 1024 * 1024; // 256mb, same as storage chunk size
    static constexpr unsigned disk_size_bytes = sizeof(uint32_t);
    static constexpr size_t max_size =
        max_disk_size + max_number_of_children * KECCAK256_SIZE;
    using BytesAllocator = allocators::malloc_free_allocator<std::byte>;

    static allocators::detail::type_raw_alloc_pair<
        std::allocator<Node>, BytesAllocator>
    pool();
    static size_t get_deallocate_count(Node *);

    using Deleter = allocators::unique_ptr_aliasing_allocator_deleter<
        std::allocator<Node>, BytesAllocator, &Node::pool,
        &Node::get_deallocate_count>;
    using UniquePtr = std::unique_ptr<Node, Deleter>;

    /* Storage starts here */
    /* 16-bit mask for children */
    uint16_t mask{0};

    struct bitpacked_storage_t
    {
        /* does node have a value, value_len is not necessarily positive */
        bool has_value : 1 {false};
        bool path_nibble_index_start : 1 {false};
        /* size (in byte) of intermediate cache for branch hash */
        uint8_t data_len : 6 {0};
    } bitpacked{0};

    static_assert(sizeof(bitpacked) == 1);

    uint8_t path_nibble_index_end{0};
    /* size (in byte) of user-passed leaf data */
    uint32_t value_len{0};
    /* A note on definition of node version:
    version(leaf node) corresponds to the block number when it was
    last updated.
    version(interior node) >= max(version of the leaf nodes under its prefix),
    it is greater than only when the latest update in the subtrie contains only
    deletions. */
    int64_t version{0};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    unsigned char fnext_data[0];
#pragma GCC diagnostic pop

    template <class... Args>
    static UniquePtr make(size_t bytes, Args &&...args)
    {
        MONAD_DEBUG_ASSERT(bytes <= Node::max_size);
        return allocators::allocate_aliasing_unique<
            std::allocator<Node>,
            BytesAllocator,
            &pool,
            &get_deallocate_count>(
            bytes,
            prevent_public_construction_tag{},
            std::forward<Args>(args)...);
    }

    Node(prevent_public_construction_tag);
    Node(
        prevent_public_construction_tag, uint16_t mask,
        std::optional<byte_string_view> value, size_t data_size,
        NibblesView path, int64_t version);
    Node(Node const &) = delete;
    Node(Node &&) = default;
    ~Node();

    unsigned to_child_index(unsigned branch) const noexcept;

    unsigned number_of_children() const noexcept;

    //! fnext array that stores physical chunk offset of each child
    chunk_offset_t const fnext(unsigned index) const noexcept;
    void set_fnext(unsigned index, chunk_offset_t) noexcept;

    //! fastlist min_offset array
    unsigned char *child_min_offset_fast_data() noexcept;
    unsigned char const *child_min_offset_fast_data() const noexcept;
    compact_virtual_chunk_offset_t
    min_offset_fast(unsigned index) const noexcept;
    void set_min_offset_fast(
        unsigned index, compact_virtual_chunk_offset_t) noexcept;
    //! slowlist min_offset array
    unsigned char *child_min_offset_slow_data() noexcept;
    unsigned char const *child_min_offset_slow_data() const noexcept;
    compact_virtual_chunk_offset_t
    min_offset_slow(unsigned index) const noexcept;
    void set_min_offset_slow(
        unsigned index, compact_virtual_chunk_offset_t) noexcept;

    //! subtrie min version array
    unsigned char *child_min_version_data() noexcept;
    unsigned char const *child_min_version_data() const noexcept;
    int64_t subtrie_min_version(unsigned index) const noexcept;
    void set_subtrie_min_version(unsigned index, int64_t version) noexcept;

    //! data_offset array
    unsigned char *child_off_data() noexcept;
    unsigned char const *child_off_data() const noexcept;
    uint16_t child_data_offset(unsigned index) const noexcept;

    unsigned child_data_len(unsigned index) const;
    unsigned child_data_len();

    //! path
    unsigned char *path_data() noexcept;
    unsigned char const *path_data() const noexcept;
    unsigned path_nibbles_len() const noexcept;
    bool has_path() const noexcept;
    unsigned path_bytes() const noexcept;
    NibblesView path_nibble_view() const noexcept;
    unsigned path_start_nibble() const noexcept;

    //! value
    unsigned char *value_data() noexcept;
    unsigned char const *value_data() const noexcept;
    bool has_value() const noexcept;
    byte_string_view value() const noexcept;
    std::optional<byte_string_view> opt_value() const noexcept;

    //! data
    unsigned char *data_data() noexcept;
    unsigned char const *data_data() const noexcept;
    byte_string_view data() const noexcept;

    //! child data
    unsigned char *child_data() noexcept;
    unsigned char const *child_data() const noexcept;
    byte_string_view child_data_view(unsigned index) const noexcept;
    unsigned char *child_data(unsigned index) noexcept;
    void set_child_data(unsigned index, byte_string_view data) noexcept;

    // On disk layout: preceeding the node data is the disk size of the node.
    uint32_t get_disk_size() const noexcept;
};

void serialize_node(unsigned char *write_pos, Node const &);

Node *parse_node(unsigned char const *mmap_address, chunk_offset_t offset);

MONAD_MPT2_NAMESPACE_END
