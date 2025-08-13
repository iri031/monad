#pragma once

#include <category/mpt/request.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>
#include <category/mpt2/config.hpp>
#include <category/storage/util.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

using chunk_offset_t = MONAD_STORAGE_NAMESPACE::chunk_offset_t;
using chunk_offset_t_hasher = MONAD_STORAGE_NAMESPACE::chunk_offset_t_hasher;
using file_offset_t = MONAD_STORAGE_NAMESPACE::file_offset_t;

using MONAD_STORAGE_NAMESPACE::CPU_PAGE_SIZE;
using MONAD_STORAGE_NAMESPACE::DISK_PAGE_BITS;
using MONAD_STORAGE_NAMESPACE::DISK_PAGE_SIZE;
using MONAD_STORAGE_NAMESPACE::DMA_PAGE_BITS;
using MONAD_STORAGE_NAMESPACE::DMA_PAGE_SIZE;
using MONAD_STORAGE_NAMESPACE::INVALID_OFFSET;

using MONAD_STORAGE_NAMESPACE::round_down_align;
using MONAD_STORAGE_NAMESPACE::round_up_align;

using MONAD_MPT_NAMESPACE::INVALID_BRANCH;
using MONAD_MPT_NAMESPACE::INVALID_PATH_INDEX;
using MONAD_MPT_NAMESPACE::MIN_HISTORY_LENGTH;

using MONAD_MPT_NAMESPACE::bitmask_index;
using MONAD_MPT_NAMESPACE::compact_virtual_chunk_offset_t;
using MONAD_MPT_NAMESPACE::empty_trie_hash;
using MONAD_MPT_NAMESPACE::INVALID_COMPACT_VIRTUAL_OFFSET;
using MONAD_MPT_NAMESPACE::INVALID_VIRTUAL_OFFSET;
using MONAD_MPT_NAMESPACE::MIN_COMPACT_VIRTUAL_OFFSET;
using MONAD_MPT_NAMESPACE::virtual_chunk_offset_t;
using MONAD_MPT_NAMESPACE::virtual_chunk_offset_t_hasher;

//! serilaize a value as it is to a byte string
template <std::integral V>
inline byte_string serialize(V n)
{
    static_assert(std::endian::native == std::endian::little);
    auto arr = std::bit_cast<std::array<unsigned char, sizeof(V)>>(n);
    return byte_string{arr.data(), arr.size()};
}

MONAD_MPT2_NAMESPACE_END
