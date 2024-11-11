#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHashBuffer
{
    static constexpr unsigned N = 256;

    virtual uint64_t n() const = 0;
    virtual void set(uint64_t const n, bytes32_t const &h) = 0;
    virtual bytes32_t const &get(uint64_t const n) const = 0;
};

class BlockHashBufferFinal : BlockHashBuffer
{
    bytes32_t b_[N];
    uint64_t n_;

public:
    BlockHashBufferFinal();

    virtual uint64_t n() const override
    {
        return n_;
    };

    virtual void set(uint64_t const n, bytes32_t const &h) override
    {
        MONAD_ASSERT(!n_ || n == n_);
        b_[n % N] = h;
        n_ = n + 1;
    }

    virtual bytes32_t const &get(uint64_t const n) const override
    {
        MONAD_ASSERT(n < n_ && n + N >= n_);
        return b_[n % N];
    }
};

class BlockHashBufferProposal : BlockHashBuffer
{
    uint64_t const n_;
    BlockHashBufferFinal const &buf_;
    std::vector<bytes32_t> hash_;

    BlockHashBufferProposal(bytes32_t const &, BlockHashBufferFinal const &);
    BlockHashBufferProposal(bytes32_t const &, BlockHashBufferProposal const &);

    virtual uint64_t n() const override = 0;
    virtual void set(uint64_t, bytes32_t const &) override;
    virtual bytes32_t const &get(uint64_t) const override;
};

// uint64_t n;
// uint64_t n_round;
// BlockHashBuffer buf;
// std::deque<BlockHashBufferProposal> proposals;
//
// void finalize(uint64_t const round, bytes32_t const &hash)
//{
//     buf.set(n, hash);
//     for (size_t i = 0; i < (round - n_round); ++i) {
//         proposals.pop_front();
//     }
// }

MONAD_NAMESPACE_END
