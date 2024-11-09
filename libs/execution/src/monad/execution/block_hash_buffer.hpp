#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer
{
    static constexpr unsigned N = 256;

    bytes32_t b_[N];
    uint64_t n_;

public:
    BlockHashBuffer();

    void set(uint64_t const n, bytes32_t const &h)
    {
        MONAD_ASSERT(!n_ || n == n_);
        b_[n % N] = h;
        n_ = n + 1;
    }

    bytes32_t const &get(uint64_t const n) const
    {
        MONAD_ASSERT(n < n_ && n + N >= n_);
        return b_[n % N];
    }
};

class BlockHashChain
{
    template <class Key, class T>
    using Map = ankerl::unordered_dense::segmented_map<Key, T>;

    Map<uint64_t, BlockHashBuffer> chain_;
    Map<uint64_t, std::vector<uint64_t>> gc_;
    uint64_t last_finalized_block_;

public:
    BlockHashChain(
        uint64_t const last_finalized_block =
            std::numeric_limits<uint64_t>::max())
        : last_finalized_block_(last_finalized_block)
    {
    }

    BlockHashBuffer &next_buffer(
        uint64_t const block_number, uint64_t const round,
        uint64_t const parent_round)
    {
        auto [it1, inserted] =
            chain_.try_emplace(parent_round, BlockHashBuffer());
        auto it2 = gc_.try_emplace(block_number, std::vector<uint64_t>{}).first;
        if (MONAD_UNLIKELY(inserted)) {
            MONAD_ASSERT(round == parent_round);
            it2->second.emplace_back(round);
            return it1->second;
        }
        else {
            // TODO: This copies the the entire BlockHashBufer (8k) every time.
            // We can optimize for the happy path and only copy on fork.
            auto it3 = chain_.try_emplace(round, it1->second).first;
            it2->second.emplace_back(round);
            return it3->second;
        }
    }

    void finalize(uint64_t const block_number, uint64_t const round)
    {
        // drop chains from previous blocks
        for (uint64_t b = last_finalized_block_ + 1; b < block_number; ++b) {
            auto it = gc_.find(b);
            MONAD_ASSERT(it != gc_.end());
            for (auto r : it->second) {
                chain_.erase(r);
            }
            gc_.erase(it);
        }

        // current block - keep only the finalized round
        auto it = gc_.find(block_number);
        MONAD_ASSERT(it != gc_.end());
        for (auto r : it->second) {
            if (r != round) {
                chain_.erase(r);
            }
        }

        last_finalized_block_ = block_number;
    }
};

MONAD_NAMESPACE_END
