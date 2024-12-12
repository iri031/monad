#include <monad/execution/parallel_commit_system.hpp>

MONAD_NAMESPACE_BEGIN

#if SEQUENTIAL
void ParallelCommitSystem::waitForPrevTransactions(txindex_t myindex) {
    promises[myindex].get_future().wait();
}

void ParallelCommitSystem::notifyDone(txindex_t myindex) {
    promises[myindex + 1].set_value();
}

ParallelCommitSystem::ParallelCommitSystem(txindex_t num_transactions) {
    promises = new boost::fibers::promise<void>[num_transactions + 1];
    promises[0].set_value();
}

ParallelCommitSystem::~ParallelCommitSystem() {
    delete[] promises;
}

void ParallelCommitSystem::declareFootprint(txindex_t, const std::set<evmc::address> *) {
}
#else

ParallelCommitSystem::ParallelCommitSystem(txindex_t num_transactions) 
    : status_(num_transactions),
      all_committed_ub(0),
      footprints_(num_transactions, nullptr)
        //,pending_footprints_(num_transactions)// not used currently
{
    for (auto& status : status_) {
        status.store(TransactionStatus::STARTED);
    }
    
    promises = new boost::fibers::promise<void>[num_transactions + 1];
    promises[0].set_value();
}

void ParallelCommitSystem::registerAddressAccessedBy(const evmc::address& addr, txindex_t index) {
    tbb::concurrent_set<txindex_t> * set;
    {
        auto it = transactions_accessing_address_.find(addr);
        if (it == transactions_accessing_address_.end()) {
            it = transactions_accessing_address_.insert({addr, new tbb::concurrent_set<txindex_t>()}).first;
        }
        set=it->second;
    }
    //because nobody will ever change the set pointer in the map, we do set->insert after `it` goes out of scope, thus releasing the lock, and allowing other threads to concurrently insert into the set.
    // if this address was not in the map before, `it` may hold a write lock on the set, thus preventing other threads from accessing the set.
    set->insert(index);
}

void ParallelCommitSystem::declareFootprint(txindex_t myindex, const std::set<evmc::address> *footprint) {
    footprints_[myindex] = footprint;
    if (footprint) {
        for (const auto& addr : *footprint) {
            registerAddressAccessedBy(addr, myindex);
        }
    }

    tryUnblockTransactionsStartingFrom(myindex);

    // update status_[myindex] from STARTED to FOOTPRINT_COMPUTED, while preserving the _UNBLOCKED part which previous transactions may change concurrently when they notifyDone
    auto current_status = status_[myindex].load();
    // on non-first iterations, current_status comes from the CAS at the end of the previous iteration
    assert(current_status == TransactionStatus::STARTED ||
        current_status == TransactionStatus::STARTED_UNBLOCKED);

    auto new_status = (current_status == TransactionStatus::STARTED) ? 
                TransactionStatus::FOOTPRINT_COMPUTED :
                (current_status == TransactionStatus::STARTED_UNBLOCKED) ?
                    TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED :
                    current_status;
        
    if (!status_[myindex].compare_exchange_weak(current_status, new_status)) {
        assert(current_status == TransactionStatus::STARTED_UNBLOCKED);
        current_status = TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
    }
}

ParallelCommitSystem::~ParallelCommitSystem() {
    delete[] promises;
    // Remove delete[] footprints_ - vectors clean up automatically
}

void ParallelCommitSystem::waitForPrevTransactions(txindex_t myindex) {
    auto current_status = status_[myindex].load();
    assert(current_status == TransactionStatus::FOOTPRINT_COMPUTED ||
        current_status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);

    if (current_status == TransactionStatus::FOOTPRINT_COMPUTED) {
        // Attempt to change the status to WAITING_FOR_PREV_TRANSACTIONS
        if (status_[myindex].compare_exchange_weak(current_status, TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS)) {
            promises[myindex].get_future().wait();
            //status_[myindex].store(TransactionStatus::COMMITTING); this will be done by the previous transaction who wakes this one up
        }
        else {
            assert(current_status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);
            status_[myindex].store(TransactionStatus::COMMITTING);
        }
    }
}

bool ParallelCommitSystem::isUnblocked(TransactionStatus status) {
    return status > TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS || status == TransactionStatus::STARTED_UNBLOCKED || status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
}

ParallelCommitSystem::txindex_t ParallelCommitSystem::highestLowerIndexAccessingAddress(txindex_t index, const evmc::address& addr) {
    auto it = transactions_accessing_address_.find(addr);
    if (it == transactions_accessing_address_.end()) {
        return std::numeric_limits<txindex_t>::max();
    }
    auto set = it->second;
    auto it2 = set->begin();
    while (it2 != set->end() && *it2 < index) {
        ++it2;
    }
    return *it2;
}

bool ParallelCommitSystem::tryUnblockTransaction(TransactionStatus status, txindex_t index) {
    if (isUnblocked(status)) {
        return true;
    }

    auto all_committed_ub_ = all_committed_ub.load();
    if (all_committed_ub_ >= index-1) {
        unblockTransaction(status, index);
        return true;
    }
    //status=status_[index].load(); // get the more uptodate value, but not essential for correctness
    if (status == TransactionStatus::STARTED) {
        return false;
    }
    if (status == TransactionStatus::FOOTPRINT_COMPUTED || status==TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS) {
        auto footprint = footprints_[index];
        assert(footprint);
        for (const auto& addr : *footprint) {
            auto highest_prev = highestLowerIndexAccessingAddress(index, addr);
            if (highest_prev == std::numeric_limits<txindex_t>::max() && status_[highest_prev].load() != TransactionStatus::COMMITTED)
                return false;
        }
        unblockTransaction(status, index);
        return true;
    }
    return false;
}

void ParallelCommitSystem::tryUnblockTransactionsStartingFrom(txindex_t start) {
    for (auto index = start; index < status_.size(); ++index) {
        tryUnblockTransaction(status_[index].load(), index);
    }
    // unblock or wake up later transactions
    // once we hit a transaction whose footprint is not yet computed,
    // we cannot wake up or unblock transactions after that transaction
    // every transaction accesses at least 1 account and the uncomputed footprint may include that account.
    auto num_transactions = status_.size();
    for(auto index = start; index < num_transactions; ++index) {
        auto current_status = status_[index].load();
        tryUnblockTransaction(current_status, index);
        if (current_status == TransactionStatus::STARTED || current_status == TransactionStatus::STARTED_UNBLOCKED)
            break;// footprint has not been computed yet, so it may conflict with any transaction after index
    }
}

void ParallelCommitSystem::notifyDone(txindex_t myindex) {
    status_[myindex].store(TransactionStatus::COMMITTED);
    updateLastCommittedUb();
    tryUnblockTransactionsStartingFrom(myindex+1); // unlike before, the transaction myindex+1 cannot necesssarily be unblocked here because some transaction before myindex may not have committed and may have conflicts
}

void ParallelCommitSystem::updateLastCommittedUb() {
    auto newUb = all_committed_ub.load() + 1;
    while (newUb < status_.size()) {
        if (status_[newUb].load() != TransactionStatus::COMMITTED) {
            break;
        }
        newUb++;
    }
    advanceLastCommittedUb(newUb);
}

void ParallelCommitSystem::advanceLastCommittedUb(txindex_t minValue) {
    txindex_t old_value = all_committed_ub.load();
    while (old_value < minValue) {
        if (all_committed_ub.compare_exchange_weak(old_value, minValue)) {
            break;
        }
    }
}

#endif

MONAD_NAMESPACE_END
