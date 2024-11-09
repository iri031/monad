#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash_buffer.hpp>

MONAD_NAMESPACE_BEGIN

BlockHashBuffer::BlockHashBuffer()
    : b_{}
    , n_{0}
{
    for (auto &h : b_) {
        h = NULL_HASH;
    }
}

uint64_t BlockHashBuffer::n() const
{
    return n_;
};

bytes32_t const &BlockHashBuffer::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + N >= n_);
    return b_[n % N];
}

void BlockHashBuffer::set(uint64_t const n, bytes32_t const &h)
{
    MONAD_ASSERT(!n_ || n == n_);
    b_[n % N] = h;
    n_ = n + 1;
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &h, uint64_t const round, uint64_t const parent_round,
    BlockHashBufferBase const &buf)
    : n_{buf.n() + 1}
    , round_{round}
    , parent_round_{parent_round}
    , buf_{&buf}
    , deltas_{h}
{
}

BlockHashBufferProposal::BlockHashBufferProposal(
    bytes32_t const &h, uint64_t const round, uint64_t const parent_round,
    BlockHashBufferProposal const &parent)
    : n_{parent.n_ + 1}
    , round_{round}
    , parent_round_{parent_round}
    , buf_{parent.buf_}
{
    MONAD_ASSERT(parent_round < round);
    MONAD_ASSERT(n_ > 0 && n_ > buf_->n());
    deltas_.push_back(h);
    deltas_.insert(deltas_.end(), parent.deltas_.begin(), parent.deltas_.end());
    deltas_.resize(n_ - buf_->n());
}

uint64_t BlockHashBufferProposal::n() const
{
    return n_;
}

uint64_t BlockHashBufferProposal::round() const
{
    return round_;
}

uint64_t BlockHashBufferProposal::parent_round() const
{
    return parent_round_;
}

bytes32_t const &BlockHashBufferProposal::h() const
{
    return deltas_.front();
}

bytes32_t const &BlockHashBufferProposal::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + N >= n_);
    size_t const idx = n_ - n - 1;
    if (idx < deltas_.size()) {
        return deltas_.at(idx);
    }
    return buf_->get(n);
}

BlockHashChain::BlockHashChain(BlockHashBuffer &buf)
    : buf_{buf}
    , finalized_{buf.n() == 0 ? static_cast<uint64_t>(-1) : buf.n()}
{
}

BlockHashBufferBase const &BlockHashChain::propose(
    bytes32_t const &hash, uint64_t const round, uint64_t const parent_round)
{
    for (auto it = proposals_.rbegin(); it != proposals_.rend();) {
        if (it->round() == round) {
            // delete duplicate
            it = std::reverse_iterator(proposals_.erase(std::next(it).base()));
            continue;
        }
        else if (it->round() == parent_round) {
            return proposals_.emplace_back(hash, round, parent_round, *it);
        }
        ++it;
    }
    return proposals_.emplace_back(hash, round, parent_round, buf_);
}

BlockHashBufferBase const &BlockHashChain::finalize(uint64_t const round)
{
    auto const to_finalize = finalized_ + 1;

    MONAD_ASSERT(to_finalize == 0 || round > finalized_);
    MONAD_ASSERT(!proposals_.empty());

    auto winner_it = proposals_.begin();
    for (; winner_it != proposals_.end() && winner_it->round() != round;
         ++winner_it) {
    }
    MONAD_ASSERT(winner_it->round() == round);
    MONAD_ASSERT((winner_it->n() - 1) == to_finalize);

    buf_.set(to_finalize, winner_it->h());
    finalized_ = to_finalize;

    // cleanup chains
    uint64_t const to_delete = winner_it->parent_round();
    for (auto it = proposals_.begin();
         it != proposals_.end() && it->parent_round() == to_delete;) {
        it = proposals_.erase(it);
    }

    return buf_;
}

MONAD_NAMESPACE_END
