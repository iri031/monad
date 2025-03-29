#pragma once

#include <monad/config.hpp>
#include <atomic>
#include <cstdint>
#include <cassert>


MONAD_NAMESPACE_BEGIN

// store a set of transactions indices encoded as a bitset. 
// currently supports only transaction indices< 64^64 elements, but can be extended to 64^64^64 by using a 3-level array.
// contains_any_element_less than requires at most 2 atomic loads.
// unset_bit_update_index requires 2 fetch_ands
class ConcurrentTxSet {

public:
    void reset() {
        for (uint64_t i = 0; i < 64; i++) {
            membership[i] = 0;
        }
        index = 0;
        lastCommittedIndex.store(0);
    }

    ConcurrentTxSet() {
        reset();
    }
    void insert(uint64_t bit_index) {
        uint64_t mask = 1ULL << (bit_index % 64);
        uint64_t word_index = bit_index / 64;
        uint64_t old_word = membership[word_index];
        membership[word_index] = old_word | mask;
        if (old_word == 0) {
            index = index | (1 << word_index);
        }
    }

    bool contains(uint64_t bit_index) const {
        return (membership[bit_index / 64] & (1 << (bit_index % 64))) != 0;
    }

    // Returns true if `bits` has any set bit in the inclusive subrange
    // [fromBit..toBit].
    static bool checkChunkRange(uint64_t bits, uint64_t fromBit, uint64_t toBit)
    {
        assert(fromBit <= toBit);

        // Build a mask that has bits [fromBit..toBit] set, and the rest
        // cleared.
        //   ~0ULL << fromBit  => sets bits from `fromBit` to 63
        //   ~0ULL >> (63 - toBit) => sets bits from 0 to `toBit`
        // The intersection (bitwise AND) gives bits [fromBit..toBit].
        uint64_t mask = (~0ULL << fromBit) & (~0ULL >> (63 - toBit));

        return (bits & mask) != 0ULL;
    }

    bool contains_uncommitted_index_less_than(uint64_t idx) const
    {
        uint64_t c = lastCommittedIndex.load(std::memory_order_acquire);

        if (idx <= c + 1) {// redundant check?
            return false;
        }

        uint64_t start = c + 1;
        uint64_t end = idx - 1;
        // membership covers IDs [0..4095].
        static uint64_t const MAX_ID = 4095;
        if (start > MAX_ID) {
            // No membership ID to check if start is beyond 4095
            return false;
        }
        assert(end <= MAX_ID);
        if (start > end) {
            return false;
        }

        // Identify which 64-bit chunks the IDs [start..end] belong to
        uint64_t startChunk = start >> 6; // start / 64
        uint64_t endChunk = end >> 6; // end   / 64
        uint64_t startBit = start & 63; // start % 64
        uint64_t endBit = end & 63; // end   % 64

        if (startChunk == endChunk) {
            return checkChunkRange(membership[startChunk], startBit, endBit);
        }

        if (checkChunkRange(membership[startChunk], startBit, 63)) {
            return true;
        }

        if (endChunk > startChunk + 1 && checkChunkRange(index, startChunk+1, endChunk-1)) {
            return true;
        }

        if (checkChunkRange(membership[endChunk], 0, endBit)) {
            return true;
        }

        return false;
    }

    void commit(uint64_t idx) {
        uint64_t current = lastCommittedIndex.load();
        while (current < idx) {
            if (lastCommittedIndex.compare_exchange_strong(current, idx)) {
                break;
            }
        }
    }


private:

    uint64_t membership[64];// transaction i (i<64^64) belongs to the set if membership[i/64] has bit i%64 from LSB/RHS set.
    // conceptual layout of bits in`
    // membership[1](bit127, bit126, ..., bit64), membership[0](bit63, bit62, ..., bit0)
    // only read-only races are allwed on this field
    
    uint64_t index;// ith bit from LSB/RHS (mask 1<<i) here is set iff membership[i] has any bit set, i.e. is nonzero
    // only read-only races are allwed on this field

    std::atomic<uint64_t> lastCommittedIndex;// any index above this is not considered a member regardless of the value of the fields above. r/w races are allowed

};


MONAD_NAMESPACE_END