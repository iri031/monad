#pragma once

#include <category/mpt2/compute.hpp> // TODO:
#include <category/mpt2/node.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

struct ChildData
{
    Node::UniquePtr node{nullptr}; // if value means child node is newly created
                                   // and not written to disk yet
    chunk_offset_t offset{INVALID_OFFSET}; // physical offsets
    unsigned char data[32] = {0}; // max 32 bytes of data
    int64_t subtrie_min_version{std::numeric_limits<int64_t>::max()};
    compact_virtual_chunk_offset_t min_offset_fast{
        INVALID_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t min_offset_slow{
        INVALID_COMPACT_VIRTUAL_OFFSET};
    uint8_t branch{INVALID_BRANCH};
    uint8_t data_size{0};

    bool is_valid()
    {
        return branch != INVALID_BRANCH;
    }

    bool need_write_to_disk()
    {
        return node != nullptr && offset == INVALID_OFFSET;
    }

    void erase()
    {
        branch = INVALID_BRANCH;
        node.reset();
    }

    void finalize(Node::UniquePtr node, Compute &compute)
    {
        MONAD_DEBUG_ASSERT(is_valid());
        MONAD_ASSERT(node != nullptr);
        this->node = std::move(node);
        auto const length = compute.compute(data, ptr);
        MONAD_DEBUG_ASSERT(length <= std::numeric_limits<uint8_t>::max());
        data_size = static_cast<uint8_t>(length);
        subtrie_min_version = calc_min_version(ptr);
    }

    void copy_old_child(Node &old, unsigned const branch)
    {
        MONAD_DEBUG_ASSERT(branch < 16);
        this->branch = static_cast<uint8_t>(branch);
        auto const index = old.to_child_index(branch);
        auto const old_data = old.child_data_view(index);
        memcpy(&data, old_data.data(), old_data.size());
        MONAD_DEBUG_ASSERT(
            old_data.size() <= std::numeric_limits<uint8_t>::max());
        data_size = static_cast<uint8_t>(old_data.size());

        offset = old.fnext(index);
        min_offset_fast = old.min_offset_fast(index);
        min_offset_slow = old.min_offset_slow(index);
        subtrie_min_version = old.subtrie_min_version(index);
    }
};

MONAD_MPT2_NAMESPACE_END
