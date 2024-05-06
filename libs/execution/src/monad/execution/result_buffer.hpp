#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>

#include <limits>

MONAD_NAMESPACE_BEGIN

// TODO: add support for non-zero delay
class ResultBuffer
{
    size_t const n_;

public:
    static constexpr auto NONE = std::numeric_limits<size_t>::max();

    explicit ResultBuffer(size_t n);

    Receipt::Bloom get_bloom(Receipt::Bloom const &) const;
    uint64_t get_gas(uint64_t gas) const;
    void push(Receipt::Bloom const &, uint64_t gas);
};

static_assert(sizeof(ResultBuffer) == 8);
static_assert(alignof(ResultBuffer) == 8);

MONAD_NAMESPACE_END
