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
#include <tbb/concurrent_unordered_set.h>

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

    /*
    * declareFootprint is a promise that this transaction will not read/write any account other than those in *footprint
    * footprint=null means that it can read/write any account, e.g. when the callchain cannot be predicted
    */
    void declareFootprint(txindex_t myindex, const std::set<evmc::address> *footprint);

    ParallelCommitSystem(txindex_t num_transactions);

    ~ParallelCommitSystem();

    private:
#if SEQUENTIAL//ideally, we should use PIMPL and move the private state to the cpp files, one for the sequential impl and one for the parallel impl
    boost::fibers::promise<void> *promises;
#else
    enum class TransactionStatus : uint8_t
    {
        STARTED,
        FOOTPRINT_COMPUTED,
        COMMITTED
    };
    std::vector<std::atomic<TransactionStatus>> status_;
    std::atomic<txindex_t> all_committed_ub; // all transactions with index <= all_committed_ub have committed their changes to block_state. this ub will not be tight as we cannot update it atomically with other fields. this field is used to optimize
    std::unordered_map<evmc::address, std::set<txindex_t>>
        transactions_accessing_address_;//this excludes the transactions with "Any address" footprint
    std::vector<const std::set<evmc::address> *>
        footprints_; // can use a shared_ptr but that will increase the
                     // memory usage. with FM, shared_ptr doesnt buy much
                     // nullptr means "Any address" footprint (any address can be read/written)
                     // only transaction i updates the ith element, only once. after that, it will update status_[i] from STARTED to FOOTPRINT_COMPUTED. 
                     // other transactions will not read this until status_[i] is updated to FOOTPRINT_COMPUTED or COMMITTED.
                     // therefore we do not need atomics.

    std::vector<tbb::concurrent_unordered_set<evmc::address>>
        pending_footprints_; // the addresses that some uncommitted transaction may still be accessing. 
        // main invariant: any previous transaction accessing address in footprints_[i] but not in pending_footprints_[i] must committed already.
        // pending_footprints_[i] can be updated by transaction with index less than j. such updates can only delete elements.
        // this field is just for optimization.
#endif
};
MONAD_NAMESPACE_END
