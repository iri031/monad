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

#include <evmc/evmc.h>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN
#define SEQUENTIAL 1
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
    std::vector<std::atomic<TransactionStatus>> status_;
    std::unordered_map<evmc::address, std::set<txindex_t>>
        transactions_accessing_address_;
    std::vector<std::atomic<const std::set<evmc::address> *>>
        footprints_; // can use a shared_ptr but that will increase the
                     // memory usage. with FM, shared_ptr doesnt buy much
#endif
};
MONAD_NAMESPACE_END
