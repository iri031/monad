#include "parallel_commit_system.hpp"

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
    : status_(num_transactions, TransactionStatus::STARTED)
      ,all_committed_ub(0)
      ,footprints_(num_transactions, nullptr)
      //,pending_footprints_(num_transactions)// not used currently
{
    promises = new boost::fibers::promise<void>[num_transactions + 1];
    promises[0].set_value();
}

void ParallelCommitSystem::declareFootprint(txindex_t myindex, const std::set<evmc::address> *footprint) {
    footprints_[myindex] = footprint;
    if (footprint) {
        for (const auto& addr : *footprint) {
            transactions_accessing_address_.insert({addr, myindex});
        }
    }

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
            current_status = TransactionStatus::COMMITTING;
        }
    }
}

void ParallelCommitSystem::notifyDone(txindex_t myindex) {
    // TODO: implement
}

#endif

MONAD_NAMESPACE_END
