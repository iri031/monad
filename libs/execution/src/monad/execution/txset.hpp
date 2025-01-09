#pragma once

#include <monad/config.hpp>
#include <atomic>
#include <cstdint>
#include <oneapi/tbb/concurrent_set.h>
#include <cassert>


MONAD_NAMESPACE_BEGIN

// store a set of transactions indices encoded as a bitset. 
// currently supports only transaction indices< 64^64 elements, but can be extended to 64^64^64 by using a 3-level array.
// contains_any_element_less than requires at most 2 atomic loads.
// unset_bit_update_index requires 2 fetch_ands
class ConcurrentTxSet {

public:
    ConcurrentTxSet() : index(0) {
        for (uint64_t i = 0; i < 64; i++) {
            membership[i].store(0);
        }
    }
    //nobody will read the index at this time so we skip the index update to a populate_index call later that happens before the index starts being read.
    // this function will be called concurrently thouth, just after compute_sender.
    void set_bit_without_index_upddate(uint64_t bit_index)
    {
        uint64_t mask = 1ULL << (bit_index % 64);
        std::atomic<uint64_t> &word = membership[bit_index / 64];
        word.fetch_or(mask);
    }

    // post: cannot really guarantee that the index is consistent because some other thread may be in the middle of a call to this function
    // the commit point is when the membership array is updated. 
    // the index is just an optimization (laggy cache) with the guaranttee that if the index bit is 0, means the word is 0, but not the other way around.
    void unset_bit_update_index(uint64_t bit_index){
        uint64_t mask = 1ULL << (bit_index % 64);
        uint64_t word_index = bit_index / 64;
        std::atomic<uint64_t> &word = membership[word_index];
        uint64_t old_word = word.fetch_and(~mask);
        uint64_t new_word = old_word & ~mask;
        if (new_word == 0) {
            index.fetch_and(~(1 << word_index));
        }
    }

    // preost: exclusive access to this object
    //post: the index is consistent with the membership array
    void pupulate_index() {
        uint64_t local_index = 0;
        for (uint64_t i = 0; i < 64; i++) {
            if (membership[i].load(std::memory_order_relaxed) != 0) {
                local_index |= (1ULL << i);
            }
        }
        index.store(local_index);
    }

    bool get_bit(uint64_t bit_index) const {
        return (membership[bit_index / 64].load() & (1 << (bit_index % 64))) != 0;
    }

    bool contains_any_element_lessthan(uint64_t bit_index) const {
        // First check the index for quick rejection of empty words
        uint64_t word_index = bit_index / 64;
        
        // Check if any words before word_index have bits set
        uint64_t index_mask = (1ULL << word_index) - 1;
        uint64_t index_bits = index.load() & index_mask;
        if (index_bits != 0) {
            return true;
        }
        //here we know that all previous words are 0.

        // Check partial word (containg bits with lower index) at word_index
        if ((index.load() & (1ULL << word_index)) != 0) {
            uint64_t bit_in_word = bit_index % 64;
            uint64_t mask = (1ULL << bit_in_word) - 1;
            return (membership[word_index].load() & mask) != 0;
        }

        return false;
    }

private:
    std::atomic<uint64_t> membership[64];// transaction i (i<64^64) belongs to the set if membership[i/64] has bit i%64 from LSB/RHS set.
    // conceptual layout of bits in`
    // membership[1](bit127, bit126, ..., bit64), membership[0](bit63, bit62, ..., bit0)
    
    std::atomic<uint64_t> index;// ith bit from LSB/RHS (mask 1<<i) here is set iff membership[i] has any bit set, i.e. is nonzero

};

void test_txset() {
    // Create an instance of the class
    // Assuming the class name is TxSet based on the context
    ConcurrentTxSet tx;

    // Test pupulate_index method
    // We cannot directly assert on private fields like index, so we assume
    // there are public methods to verify the state indirectly.

    // Test get_bit method
    // Assuming there is a way to set bits through public methods
    // For example, a method like set_bit(uint64_t bit_index)
    tx.set_bit_without_index_upddate(3); // Hypothetical method to set bit 3
    tx.set_bit_without_index_upddate(69); // Hypothetical method to set bit 69
    tx.pupulate_index();

    assert(tx.get_bit(3) == true); // Bit 3 should be set
    assert(tx.get_bit(69) == true); // Bit 69 should be set
    assert(tx.get_bit(2) == false); // Bit 2 should not be set

    // Test contains_any_element_lessthan method
    assert(tx.contains_any_element_lessthan(70) == true); // There are elements less than 70
    assert(tx.contains_any_element_lessthan(3) == false); // No elements less than 3
    assert(tx.contains_any_element_lessthan(4) == true); // There is an element less than 4
    // Test unset_bit method
    // Assuming there is a way to unset bits through public methods
    // For example, a method like unset_bit(uint64_t bit_index)
    tx.unset_bit_update_index(3); // Hypothetical method to unset bit 69

    assert(tx.get_bit(3) == false); // Bit 3 should be unset
    assert(tx.get_bit(69) == true); // Bit 69 should be unset
    assert(tx.get_bit(70) == false);
    assert(tx.get_bit(150) == false);
    assert(tx.get_bit(2) == false); // Bit 2 should still not be set

    // Test contains_any_element_lessthan method after unsetting bits
    for(uint64_t i=70; i<64*64; i++){
        assert(tx.contains_any_element_lessthan(i) == true); // No elements less than 70
    }
    assert(tx.contains_any_element_lessthan(3) == false); // No elements less than 3
    assert(tx.contains_any_element_lessthan(4) == false); // No elements less than 4

    tx.unset_bit_update_index(69); // Hypothetical method to unset bit 3
    assert(tx.get_bit(69) == false); // Bit 69 should be unset
    
    for(uint64_t i=0; i<64*64; i++){
        assert(tx.contains_any_element_lessthan(i) == false);
    }

    tx.set_bit_without_index_upddate(64); // Hypothetical method to set bit 69
    tx.pupulate_index();
    // Test contains_any_element_lessthan method after unsetting bits
    for(uint64_t i=65; i<64*64; i++){
        assert(tx.contains_any_element_lessthan(i) == true);
    }
    for(uint64_t i=0; i<64; i++){
        assert(tx.contains_any_element_lessthan(i) == false);
    }
    
}




MONAD_NAMESPACE_END