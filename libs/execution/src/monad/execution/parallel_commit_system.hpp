#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <set>
#include <atomic>
#include <unordered_map>
#include <tbb/concurrent_set.h>
#include <tbb/concurrent_unordered_map.h>
#include <oneapi/tbb/concurrent_unordered_map.h>

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>

#define MAX_TRANSACTIONS 800
MONAD_NAMESPACE_BEGIN
#define SEQUENTIAL 0

static inline int highestSetBitPos(uint64_t x) {
    if (x == 0) return -1;
    return 63 - __builtin_clzll(x);
}

template <size_t N>
class StaticBitset
{
public:
    static constexpr size_t CHUNK_COUNT = (N + 63) / 64;

    constexpr StaticBitset() : data{} {
        // Zero-initialized
    }
    void reset() {
        std::memset(data, 0, sizeof(data));
    }
    // Set a bit at the given index (no range checks in example).
    void setBit(size_t pos) {
        size_t chunkIndex = pos / 64;
        size_t bitIndex   = pos % 64;
        data[chunkIndex] |= (1ULL << bitIndex);
    }

    uint64_t findLargestSetBitInRange(size_t ge, size_t lt) const {
	if (ge >= lt) {
	    return std::numeric_limits<uint64_t>::max();
	}

	size_t lowChunk   = ge / 64;
	size_t lowOffset  = ge % 64;
	if (lt == 0) {
	    return std::numeric_limits<uint64_t>::max();
	}
	size_t highChunk  = (lt - 1) / 64;
	size_t highOffset = (lt - 1) % 64;

	// Safely make a mask of low n bits
	auto maskLowBits = [](size_t n) {
	    if (n >= 64) return 0xFFFFFFFFFFFFFFFFULL;
	    return (1ULL << n) - 1ULL;
	};

	for (size_t c = highChunk; ; c--) {
	    // Stop scanning if we've gone below lowChunk
	    if (c < lowChunk) {
		break;
	    }

	    // Start with all bits set
	    uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;

	    // If c == highChunk, mask out bits above highOffset
	    if (c == highChunk) {
		uint64_t hiMask = maskLowBits(highOffset + 1ULL);
		mask &= hiMask;
	    }

	    // If c == lowChunk, mask out bits below lowOffset
	    if (c == lowChunk) {
		uint64_t loMask = maskLowBits(lowOffset);
		mask &= ~loMask;
	    }

	    uint64_t maskedValue = data[c] & mask;
	    if (maskedValue != 0) {
		int highestBit = highestSetBitPos(maskedValue);
		return static_cast<uint64_t>(c) * 64ULL + highestBit;
	    }

	    if (c == 0) {
		// Avoid unsigned wrap-around
		break;
	    }
	}

	return std::numeric_limits<uint64_t>::max();
    }


private:
    uint64_t data[CHUNK_COUNT];
};

class ParallelCommitSystem
{
    public:
    using txindex_t = uint64_t;

    /*
    * waitForPrevTransactions will wait for any previous transaction that reads/wrotes accounts in my footprint, which must have been declared by now by calling declareFootprint
    */
    void waitForPrevTransactions(txindex_t myindex);

    /*
    * to be called after the transaction has committed its changes to block_state
    */
    void notifyDone(txindex_t myindex);

    /** 
    * declareFootprint is a promise that this transaction will not read/write any account other than those in *footprint
    * footprint=null means that it can read/write any account, e.g. when the callchain cannot be predicted.
    * the FULL ownership of footprint is transferred to this class: the caller should not use it after this call.
    * the destructor of this class will delete footprint.
    */
    void declareFootprint(txindex_t myindex, const std::set<evmc::address> *footprint);
    void compileFootprint();

    const std::set<evmc::address> *getFootprint(txindex_t myindex);

    
    ~ParallelCommitSystem();
    void waitForAllTransactionsToCommit();
    void reset(txindex_t num_transactions, monad::Address const &beneficiary);
    void earlyDestructFibers();

    private:
    monad::Address beneficiary;
    /*
    * promises[i].set_value() is only called by the transaction (in call to notifyDone) that CASes status[i] 
    * from foo to foo_unblocked or WAITING_FOR_PREV_TRANSACTIONS to COMMITTING
    */
    boost::fibers::promise<void> promises[MAX_TRANSACTIONS+1];
    txindex_t num_transactions;
#if SEQUENTIAL//ideally, we should use PIMPL and move the private state to the cpp files, 
//one for the sequential impl and one for the parallel impl. that may be a tiny bit slower due to the overhead of the indirection via the pointer.
#else
    enum class TransactionStatus : uint8_t
    {
        FOOTPRINT_COMPUTED=2, // at this stage, a transaction is speculatively executing the transaction. the footprint computation can share some computations with the transaction execution.
        FOOTPRINT_COMPUTED_UNBLOCKED=3,
        WAITING_FOR_PREV_TRANSACTIONS=4, // cannot be unblocked if it is waiting
        COMMITTING=5, // committing or retrying. must be unblocked by now
        COMMITTED=6 // must be unblocked by now
    };
    /*
    * returns true if the transaction is unblockable, i.e. all previous transactions accessing its footprint have already committed
    * status is expected to be a recent load from status_[index]
    * it is just a minor optimization to avoid calling load() on status_[index] because it is already loaded in the caller
    * 
    */
    bool tryUnblockTransaction(txindex_t all_committed_ub_, txindex_t index);
    static bool isUnblocked(TransactionStatus status);
    txindex_t highestLowerUncommittedIndexAccessingAddress(txindex_t index, const evmc::address& addr);
    void tryUnblockTransactionsStartingFrom(txindex_t all_committed_ub, txindex_t start);
    txindex_t updateLastCommittedUb(bool & alldone, txindex_t justCommittedIndex);
    /** update all_committed_below_index so that it is at least minValue */
    txindex_t advanceLastCommittedUb(txindex_t minValue);
    void registerAddressAccessedBy(const evmc::address& addr, txindex_t index);
    bool existsBlockerBefore(txindex_t all_committed_ub, txindex_t index) const;
//    bool blocksAllLaterTransactions(txindex_t index) const;
    static std::string status_to_string(TransactionStatus status);
    void notifyAllDone();// add a block index argument
    /**
    * status is expected to be a recent load from status_[index]
    * it is just a minor optimization to avoid calling load() on status_[index] because it is already loaded in the caller
    */
    void unblockTransaction(TransactionStatus status, txindex_t index);

    std::atomic<TransactionStatus> status_[MAX_TRANSACTIONS];
    /**
    * all_committed_below_index is the upper bound of the index of transactions that have committed their changes to block_state.
    * this ub will not be tight as we cannot update it atomically with other fields. this field is used to optimize
    * the check of whether all previous transactions have committed.
    */
    std::atomic<txindex_t> all_committed_below_index; 
    std::unordered_map<evmc::address, StaticBitset<MAX_TRANSACTIONS>> transactions_accessing_address_;//TODO: make the value a const sized bitset with non dynamic allocation
    /**
    * footprints_[i] is the footprint of transaction i.
    * can use a shared_ptr but that will increase the
    * memory usage. with FM, shared_ptr doesnt buy much
    * nullptr means "Any address" footprint (any address can be read/written)
    * only transaction i updates the ith element, only once. AFTER that, it will CAS status_[i] from STARTED_xxx to FOOTPRINT_COMPUTED_xxx.
    * other transactions will not read this until status_[i] is updated to FOOTPRINT_COMPUTED or greater.
    * therefore we do not need atomics.
    */
    const std::set<evmc::address> * footprints_[MAX_TRANSACTIONS];
    bool nontriv_footprint_contains_beneficiary[MAX_TRANSACTIONS]; // just a cache, can be computed from footprints_

    std::atomic<bool> all_done=false;
    StaticBitset<MAX_TRANSACTIONS> inf_footprint_txs;

    // notifyDone(i) should up fully_done[i] at the end. the guarantee is that it would not modify any field after that. 
    // currently, even after waitForAllTransactionsToCommit returns, notifyDone(i) of some transactions (especially the last ones) may be running. 
    // they incorrectly unblock a transaction of the next block if the scheduler blocks them for too long.
    // execute_block should wait for all these promises in a fiber that is parallel to the final cleanup process after waitForAllTransactionsToCommit returns.
    // that filber will up fully_done[num_transactions] at the end, which execute_block will wait for at the very end.
     //boost::fibers::promise<void> fully_done[MAX_TRANSACTIONS+1];

    /**
    * pending_footprints_[i] is a set of addresses that some uncommitted transaction may still be accessing. 
    * main invariant: any previous transaction accessing address in footprints_[i] but not in pending_footprints_[i] must committed already.
    * pending_footprints_[i] can be (concurrently) updated by any transaction with index less than i. such updates can only delete elements.
    * this field is just for optimization, so that subseqpent notifyDone calls need to check fewer addresses.
    std::vector<tbb::concurrent_unordered_set<evmc::address>>
        pending_footprints_; 
    */
#endif
};
MONAD_NAMESPACE_END
