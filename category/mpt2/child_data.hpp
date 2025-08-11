#pragma once

#include <category/core/assert.h>
#include <category/mpt2/node.hpp>
#include <category/mpt2/util.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

struct Compute;

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

    bool is_valid() const noexcept
    {
        return branch != INVALID_BRANCH;
    }

    bool need_write_to_disk() const noexcept
    {
        return node != nullptr && offset == INVALID_OFFSET;
    }

    void erase()
    {
        branch = INVALID_BRANCH;
        node.reset();
    }

    void finalize(Node::UniquePtr node, Compute &compute);

    void copy_old_child(Node &old, unsigned branch);
};

MONAD_MPT2_NAMESPACE_END
