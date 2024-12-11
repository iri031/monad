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

    void waitForTrasactionsAccessingAddresses(
        txindex_t myindex, std::vector<evmc::address> const = {});

    void notifyDone(txindex_t myindex);

    ParallelCommitSystem(txindex_t num_transactions);

    ~ParallelCommitSystem();

    private:
#if SEQUENTIAL
    boost::fibers::promise<void> *promises;
#else
#endif
};
MONAD_NAMESPACE_END
