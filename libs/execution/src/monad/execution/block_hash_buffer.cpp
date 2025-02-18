#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/db/block_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

BlockHashBuffer::BlockHashBuffer(
    immer::array<bytes32_t> const b, uint64_t const n)
    : b_{b}
    , n_{n}
{
}

BlockHashBuffer::BlockHashBuffer()
    : b_{SIZE, NULL_HASH}
    , n_{0}
{
}

uint64_t BlockHashBuffer::n() const
{
    return n_;
};

bytes32_t const &BlockHashBuffer::get(uint64_t const n) const
{
    MONAD_ASSERT(n < n_ && n + SIZE >= n_);
    return b_.at(n % SIZE);
}

BlockHashBuffer BlockHashBuffer::set(uint64_t const n, bytes32_t const &h) const
{
    MONAD_ASSERT(!n_ || n == n_);
    return BlockHashBuffer{b_.set(n % SIZE, h), n + 1};
}

BlockHashBufferChain::BlockHashBufferChain(BlockHashBuffer const finalized)
    : finalized_{finalized}
{
}

void BlockHashBufferChain::propose(
    bytes32_t const &hash, uint64_t const block_number, uint64_t const round,
    uint64_t const parent_round)
{
    BlockHashBuffer const &parent = proposed_.contains(parent_round)
                                        ? proposed_.at(parent_round)
                                        : finalized_;
    proposed_[round] = parent.set(block_number, hash);
}

void BlockHashBufferChain::finalize(uint64_t const round)
{
    if (proposed_.contains(round)) {
        BlockHashBuffer const &proposed = proposed_.at(round);
        MONAD_ASSERT(finalized_.n() == proposed.n() - 1);
        finalized_ = proposed;
    }
    proposed_.erase(proposed_.begin(), proposed_.upper_bound(round));
}

BlockHashBuffer const &BlockHashBufferChain::get(uint64_t const round) const
{
    if (proposed_.contains(round)) {
        return proposed_.at(round);
    }
    return finalized_;
}

std::pair<BlockHashBuffer, bool>
make_block_hash_buffer_from_db(mpt::Db &db, uint64_t const block_number)
{
    BlockHashBuffer buf;
    for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
         b < block_number;
         ++b) {
        auto const header = db.get(
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            b);
        if (!header.has_value()) {
            LOG_WARNING(
                "Could not query block header {} from TrieDb -- {}",
                b,
                header.error().message().c_str());
            return {buf, false};
        }
        auto const h = to_bytes(keccak256(header.value()));
        buf = buf.set(b, h);
    }

    return {buf, true};
}

std::pair<BlockHashBuffer, bool>
make_block_hash_buffer_from_blockdb(BlockDb &db, uint64_t const block_number)
{
    BlockHashBuffer buf;
    for (uint64_t b = block_number < 256 ? 1 : block_number - 255;
         b <= block_number;
         ++b) {
        Block block;
        auto const ok = db.get(b, block);
        if (!ok) {
            LOG_WARNING("Could not query block {} from blockdb.", b);
            return {buf, false};
        }
        buf = buf.set(b - 1, block.header.parent_hash);
    }

    return {buf, true};
}

MONAD_NAMESPACE_END
