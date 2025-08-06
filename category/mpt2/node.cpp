#include <category/mpt2/node.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

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
Node *
parse_node(unsigned char const *const mmap_address, chunk_offset_t const offset)
{
    MONAD_ASSERT(offset != INVALID_OFFSET);
    // read node directly from mmap
    // TODO: prefetch
    auto const *read_pos = mmap_address + offset.raw();
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

MONAD_MPT2_NAMESPACE_END
