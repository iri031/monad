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

enum class TransactionStatus : uint8_t
{
    STARTED,
    FOOTPRINT_COMPUTED,
    COMMITTED
};

class ParallelCommitSystem
{
    using txindex_t = uint32_t;
    private:

    std::vector<std::atomic<TransactionStatus>> status_;
    std::unordered_map<evmc::address, std::set<txindex_t>>
        transactions_accessing_address_;
    std::vector<std::atomic<const std::set<evmc::address> *>>
        footprints_; // can use a shared_ptr but that will increase the
                     // memory usage. with FM, shared_ptr doesnt buy much
    public:
    void declare_footprint(
        txindex_t myindex, const std::set<evmc::address> *accessed_addresses)
    {
        footprints_[myindex] = accessed_addresses;
    }

    ~ParallelCommitSystem()
    {
        for (auto &footprint : footprints_)
        {
            delete footprint;
        }
    }

    /**
     * @brief Wait for transactions that access the given addresses to finish.
     * @param myindex The index of the current transaction.
     * @param addresses The addresses to wait for. empty addresses means wait for all addresses.
     */
    void waitForTrasactionsAccessingAddresses(
        txindex_t myindex, std::vector<evmc::address> const &addresses);

    void notifyDone(txindex_t myindex);


};
MONAD_NAMESPACE_END
