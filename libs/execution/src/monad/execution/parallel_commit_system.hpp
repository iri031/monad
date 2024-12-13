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

MONAD_NAMESPACE_BEGIN
#define SEQUENTIAL 0
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

    ParallelCommitSystem(txindex_t num_transactions);

    ~ParallelCommitSystem();
    void waitForAllTransactionsToCommit();

    private:
    /*
    * promises[i].set_value() is only called by the transaction (in call to notifyDone) that CASes status[i] 
    * from foo to foo_unblocked or WAITING_FOR_PREV_TRANSACTIONS to COMMITTING
    */
    boost::fibers::promise<void> *promises; // TODO: make it a vector
#if SEQUENTIAL//ideally, we should use PIMPL and move the private state to the cpp files, 
//one for the sequential impl and one for the parallel impl. that may be a tiny bit slower due to the overhead of the indirection via the pointer.
    txindex_t num_transactions;
#else
    enum class TransactionStatus : uint8_t
    {
        STARTED=0,
        STARTED_UNBLOCKED=1,// unblocked iff all previous transactions have already committed
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
    bool tryUnblockTransaction(TransactionStatus status, txindex_t index);
    static bool isUnblocked(TransactionStatus status);
    txindex_t highestLowerUncommittedIndexAccessingAddress(txindex_t index, const evmc::address& addr);
    void tryUnblockTransactionsStartingFrom(txindex_t start);
    void updateLastCommittedUb();
    /** update all_committed_ub so that it is at least minValue */
    void advanceLastCommittedUb(txindex_t minValue);
    void registerAddressAccessedBy(const evmc::address& addr, txindex_t index);
    bool existsBlockerBefore(txindex_t index);
    bool blocksAllLaterTransactions(txindex_t index);
    /**
    * status is expected to be a recent load from status_[index]
    * it is just a minor optimization to avoid calling load() on status_[index] because it is already loaded in the caller
    */
    void unblockTransaction(TransactionStatus status, txindex_t index);

    std::vector<std::atomic<TransactionStatus>> status_;
    /**
    * all_committed_ub is the upper bound of the index of transactions that have committed their changes to block_state.
    * this ub will not be tight as we cannot update it atomically with other fields. this field is used to optimize
    * the check of whether all previous transactions have committed.
    */
    std::atomic<txindex_t> all_committed_ub; 
    tbb::concurrent_unordered_map<evmc::address, tbb::concurrent_set<txindex_t> * const> transactions_accessing_address_;
    /**
    * footprints_[i] is the footprint of transaction i.
    * can use a shared_ptr but that will increase the
    * memory usage. with FM, shared_ptr doesnt buy much
    * nullptr means "Any address" footprint (any address can be read/written)
    * only transaction i updates the ith element, only once. AFTER that, it will CAS status_[i] from STARTED_xxx to FOOTPRINT_COMPUTED_xxx.
    * other transactions will not read this until status_[i] is updated to FOOTPRINT_COMPUTED or greater.
    * therefore we do not need atomics.
    */
    std::vector<const std::set<evmc::address> *>
        footprints_; 

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
