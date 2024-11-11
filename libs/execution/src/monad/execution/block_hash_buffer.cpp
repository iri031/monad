#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash_buffer.hpp>

MONAD_NAMESPACE_BEGIN

BlockHashBufferFinal::BlockHashBufferFinal()
    : b_{}
    , n_{0}
{
    for (auto &h : b_) {
        h = NULL_HASH;
    }
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &parent_hash, BlockHashBufferFinal const &buf)
    : n_{buf.n() + 1}
    , buf_{buf}
    , hash_{parent_hash}
{
    MONAD_ASSERT(n_ > 1);
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &parent_hash, BlockHashBufferProposal const &parent)
    : n_{parent.n_ + 1}
    , buf_{parent.buf_}
{
    MONAD_ASSERT(n_ > 1 && n_ > buf_.n());
    hash_.push_back(parent_hash);
    hash_.insert(hash_.end(), parent.hash_.begin(), parent.hash_.end());
    hash_.resize(n_ - buf_.n());
}

uint64_t BlockHashBufferProposal::n() const
{
    return n_;
}

void BlockHashBufferProposal::set(uint64_t, bytes32_t const &)
{
    MONAD_ASSERT(false);
}

bytes32_t const &BlockHashBufferProposal::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + N >= n_);
    size_t const idx = n_ - n - 1;
    if (idx < hash_.size()) {
        return hash_.at(idx);
    }
    return buf_.get(n);
}

MONAD_NAMESPACE_END
