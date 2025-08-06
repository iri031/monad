#pragma once

#include <category/core/config.hpp>

#define MONAD_MPT2_NAMESPACE_BEGIN                                             \
    MONAD_NAMESPACE_BEGIN namespace mpt2                                       \
    {

#define MONAD_MPT2_NAMESPACE_END                                               \
    }                                                                          \
    MONAD_NAMESPACE_END

#define MONAD_MPT2_NAMESPACE ::monad::mpt2

MONAD_MPT2_NAMESPACE_BEGIN

static constexpr unsigned EMPTY_STRING_RLP_LENGTH = 1;
static constexpr unsigned char RLP_EMPTY_STRING = 0x80;

MONAD_MPT2_NAMESPACE_END
