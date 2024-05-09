#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/execution/result_buffer.hpp>

MONAD_NAMESPACE_BEGIN

ResultBuffer::ResultBuffer(size_t const n)
    : n_{n}
{
    MONAD_ASSERT(n_ == 0 || n == NONE);
}

Receipt::Bloom ResultBuffer::get_bloom(Receipt::Bloom const &bloom) const
{
    if (MONAD_UNLIKELY(n_ == NONE)) {
        return {};
    }
    return bloom;
}

uint64_t ResultBuffer::get_gas(uint64_t const gas) const
{
    if (MONAD_UNLIKELY(n_ == NONE)) {
        return 0;
    }
    return gas;
}

void ResultBuffer::push(Receipt::Bloom const &, uint64_t const)
{
    // TODO
}

MONAD_NAMESPACE_END
