#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/keccak.h>
#include <category/core/rlp/encode.hpp>
#include <category/mpt2/config.hpp>

#include <cstdint>
#include <cstring>

MONAD_MPT2_NAMESPACE_BEGIN

// return length of noderef
inline unsigned
to_node_reference(byte_string_view rlp, unsigned char *dest) noexcept
{
    if (MONAD_LIKELY(rlp.size() >= KECCAK256_SIZE)) {
        keccak256(rlp.data(), rlp.size(), dest);
        return KECCAK256_SIZE;
    }
    else {
        std::memcpy(dest, rlp.data(), rlp.size());
        return static_cast<unsigned>(rlp.size());
    }
}

MONAD_MPT2_NAMESPACE_END
