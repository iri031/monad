#include <monad/execution/parallel_commit_system.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/fmt/address_fmt.hpp>


MONAD_NAMESPACE_BEGIN

#if SEQUENTIAL
void ParallelCommitSystem::waitForPrevTransactions(txindex_t myindex) {
    promises.at(myindex).get_future().wait();
}

void ParallelCommitSystem::notifyDone(txindex_t myindex) {
    promises.at(myindex + 1).set_value();
}

ParallelCommitSystem::ParallelCommitSystem(txindex_t num_transactions) :promises(num_transactions+1) {
    promises.at(0).set_value();
    this->num_transactions = num_transactions;
}

ParallelCommitSystem::~ParallelCommitSystem() {
}

void ParallelCommitSystem::declareFootprint(txindex_t, const std::set<evmc::address> *) {
}

void ParallelCommitSystem::waitForAllTransactionsToCommit() {
    promises.at(num_transactions).get_future().wait();
}
#else

ParallelCommitSystem::ParallelCommitSystem(txindex_t num_transactions) 
    : status_(num_transactions),
      all_committed_below_index(0),
      footprints_(num_transactions, nullptr)
        //,pending_footprints_(num_transactions)// not used currently
{
    // promises[0] is guaranteed to be unused. so we can allocate one less in the promises array and use i-1 as the index into array.
    promises = new boost::fibers::promise<void>[num_transactions + 1];

    // Initialize first transaction as STARTED_UNBLOCKED, rest as STARTED
    if (num_transactions > 0) {
        status_[0].store(TransactionStatus::STARTED_UNBLOCKED);
    }
    else {
        promises[0].set_value();
    }
    for (size_t i = 1; i < status_.size(); i++) {
        status_[i].store(TransactionStatus::STARTED);
    }
    
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
    // because nobody will ever change the set pointer in the map, we do set->insert after `it` goes out of scope, 
    // thus releasing the lock, and allowing other threads to concurrently insert into the set.
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
        
    if (!status_[myindex].compare_exchange_strong(current_status, new_status)) {
        assert(current_status == TransactionStatus::STARTED_UNBLOCKED);
        current_status = TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
        LOG_INFO("declareFootprint: status[{}] changed from STARTED_UNBLOCKED to FOOTPRINT_COMPUTED_UNBLOCKED", myindex);
    }
    else {
        LOG_INFO("declareFootprint: status[{}] changed from {} to {}", 
            myindex, 
            status_to_string(current_status), 
            status_to_string(new_status));
    }

    if (!existsBlockerBefore(myindex)) {
        tryUnblockTransactionsStartingFrom(myindex);
    }
}

ParallelCommitSystem::~ParallelCommitSystem() {
    delete[] promises;
    // Clean up the concurrent sets stored in transactions_accessing_address_
    for (auto& pair : transactions_accessing_address_) {
        delete pair.second;
    }
    // Clean up the footprints (we own these pointers)
    for (auto footprint : footprints_) {
        if (footprint != nullptr) {
            delete footprint;
        }
    }
}

void ParallelCommitSystem::waitForPrevTransactions(txindex_t myindex) {
    auto current_status = status_[myindex].load();

    if (current_status == TransactionStatus::FOOTPRINT_COMPUTED) {
        // Attempt to change the status to WAITING_FOR_PREV_TRANSACTIONS
        if (status_[myindex].compare_exchange_strong(current_status, TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS)) {
            promises[myindex].get_future().wait();
            //status_[myindex].store(TransactionStatus::COMMITTING); this will be done by the previous transaction who wakes this one up. 
            //many transactions may try to wake this one up but only the one whose CAS to COMITTING succeeds do the set_value() (multiple calls to set_value() on the same promise is UB?)
        }
        else {
            assert(current_status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);
            status_[myindex].store(TransactionStatus::COMMITTING);
        }
    }
    else {
        assert(current_status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);
        status_[myindex].store(TransactionStatus::COMMITTING);
    }
}

bool ParallelCommitSystem::isUnblocked(TransactionStatus status) {
    return status > TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS || status == TransactionStatus::STARTED_UNBLOCKED || status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
}

void ParallelCommitSystem::unblockTransaction(TransactionStatus status, txindex_t index) {
    while (!isUnblocked(status)) {
        TransactionStatus new_status;
        if (status == TransactionStatus::STARTED) {
            new_status = TransactionStatus::STARTED_UNBLOCKED;
        } else if (status == TransactionStatus::FOOTPRINT_COMPUTED) {
            new_status = TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
        } else if (status == TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS) {
            new_status = TransactionStatus::COMMITTING;
        } else {
            assert(false);
        }

        if (status_[index].compare_exchange_strong(status, new_status)) {
            LOG_INFO("unblockTransaction: status[{}] changed from {} to {}", 
                index, 
                status_to_string(status), 
                status_to_string(new_status));
            if (new_status == TransactionStatus::COMMITTING) {
                promises[index].set_value();
            }
            break;
        }
        // state[index] only transsitions to a strictly higher value. every CAS fail means some other thread did a transition to a higher value. 
        // the increaments can only happen until COMITTED in the worst case, by which time the loop will terminate (isUnblocked(Comitted)=true).
    }
}

ParallelCommitSystem::txindex_t ParallelCommitSystem::highestLowerUncommittedIndexAccessingAddress(txindex_t index, const evmc::address& addr) {
    auto it = transactions_accessing_address_.find(addr);
    if (it == transactions_accessing_address_.end()) {
        return std::numeric_limits<txindex_t>::max();
    }
    auto set = it->second;
    LOG_INFO("indicesAccessingAddress[{}]: {}", 
        fmt::format("{}", addr),
        [&set]() {
            std::string result;
            for (auto const &i : *set) {
                result += std::to_string(i) + ", ";
            }
            return result;
        }());
    
    // Start from all_committed_below_index instead of set->begin()
    auto committed_ub = all_committed_below_index.load();
    // Finds the first element in the container that is >= committed_ub.
    auto it2 = set->lower_bound(committed_ub);
    if(it2==set->end()) {
        return std::numeric_limits<txindex_t>::max();
    }
    if(*it2>=index) {
        return std::numeric_limits<txindex_t>::max();
    }

    auto prev=*it2;
    
    // can do a binary search instead of a linear scan, but that seems tricky to do in a concurrent set
    while (true) {
        ++it2;
        if(it2==set->end()) {
            return prev;
        }
        if(*it2>=index) {
            return prev;
        }
        prev=*it2;

    }
    assert(false);
    return *it2;
}

//pre: blocksAllLaterTransactions(i) is false for all i<index
bool ParallelCommitSystem::tryUnblockTransaction(TransactionStatus status, txindex_t index) {
    if (isUnblocked(status)) {
        return true;
    }

    auto all_committed_ub_ = all_committed_below_index.load();
    if (index==all_committed_ub_) { // index-1<all_committed_ub_ <-> index -1 + 1<=all_committed_ub_ <-> index<=all_committed_ub_ <-> (index == all_committed_ub_ || index < all_committed_ub_). in the latter case, the transaction at index has already commited so we do not need to unblock it. so we can drop the last disjunct.

        unblockTransaction(status, index);
        return true;
    }
    //status=status_[index].load(); // get the more uptodate value, but not essential for correctness
    if (status == TransactionStatus::STARTED) {
        return false;
    }
    if (status == TransactionStatus::FOOTPRINT_COMPUTED || status==TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS) {
        auto footprint = footprints_[index];
        if (footprint == nullptr) {
            return false;
        }
        for (const auto& addr : *footprint) {
            auto highest_prev = highestLowerUncommittedIndexAccessingAddress(index, addr);
            assert(highest_prev<index || highest_prev == std::numeric_limits<txindex_t>::max());
            if (highest_prev != std::numeric_limits<txindex_t>::max() && status_[highest_prev].load() != TransactionStatus::COMMITTED)
                return false;// the access map may not have all entries yet. actually, it will have all relevant entries because of a precondition of this function: see comment

        }
        unblockTransaction(status, index);
        return true;
    }
    return false;
}

bool ParallelCommitSystem::existsBlockerBefore(txindex_t index) {
    auto committed_ub = all_committed_below_index.load();// transactiosn before this index cannot be blockers
    for (auto i = committed_ub; i < index; ++i) {
        if (blocksAllLaterTransactions(i)) {
            return true;
        }
    }
    return false;
}

bool ParallelCommitSystem::blocksAllLaterTransactions(txindex_t index) {
    auto status = status_[index].load();
    if (status == TransactionStatus::STARTED || status == TransactionStatus::STARTED_UNBLOCKED) {
        return true;
    }
    if (footprints_.at(index) == nullptr /* INF footprint */ && status != TransactionStatus::COMMITTED) {
        return true;
    }
    return false;
}

void ParallelCommitSystem::waitForAllTransactionsToCommit() {
    promises[status_.size()].get_future().wait();
}

//pre: blocksAllLaterTransactions(i) is false for all i<start
void ParallelCommitSystem::tryUnblockTransactionsStartingFrom(txindex_t start) {

    // unblock or wake up later transactions
    // once we hit a transaction whose footprint is not yet computed,
    // we cannot wake up or unblock transactions after that transaction
    // every transaction accesses at least 1 account and the uncomputed footprint may include that account.
    auto num_transactions = status_.size();
    for(auto index = start; index < num_transactions; ++index) {
        auto current_status = status_[index].load();
        tryUnblockTransaction(current_status, index);
        if (blocksAllLaterTransactions(index)) {
            break;
        }
    }
}

std::string ParallelCommitSystem::status_to_string(TransactionStatus status) {
    switch (status) {
        case TransactionStatus::STARTED: return "STARTED";
        case TransactionStatus::STARTED_UNBLOCKED: return "STARTED_UNBLOCKED";
        case TransactionStatus::FOOTPRINT_COMPUTED: return "FOOTPRINT_COMPUTED";
        case TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED: return "FOOTPRINT_COMPUTED_UNBLOCKED";
        case TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS: return "WAITING_FOR_PREV_TRANSACTIONS";
        case TransactionStatus::COMMITTING: return "COMMITTING";
        case TransactionStatus::COMMITTED: return "COMMITTED";
        default: assert(false);
        return "INVALID";
    }
}

void ParallelCommitSystem::notifyDone(txindex_t myindex) {
    //auto status = status_[myindex].load();
    //std::cout << "notifyDone: status of " << myindex << " is " << status_to_string(status) << std::endl;
    // assert(status == TransactionStatus::COMMITTING);
    status_[myindex].store(TransactionStatus::COMMITTED);
    updateLastCommittedUb();
    if (!existsBlockerBefore(myindex)) {
        tryUnblockTransactionsStartingFrom(myindex+1); // unlike before, the transaction myindex+1 cannot necesssarily be unblocked here because some transaction before myindex may not have committed and may have conflicts
    }
}

void ParallelCommitSystem::notifyAllDone() {
    bool old_value = false;
    if (all_done.compare_exchange_strong(old_value, true)) {
        promises[status_.size()].set_value();
    }
}

void ParallelCommitSystem::updateLastCommittedUb() {
    auto newUb = all_committed_below_index.load();
    while (newUb< status_.size()) {
        if (status_[newUb].load() != TransactionStatus::COMMITTED) {
            break;
        }
        newUb++;
    }
    advanceLastCommittedUb(newUb); // there is no use of doing it in the then case, but it is safe+clean to do it there as well
    if(newUb == status_.size()) {
        notifyAllDone();
    }
}

void ParallelCommitSystem::advanceLastCommittedUb(txindex_t minValue) {
    txindex_t old_value = all_committed_below_index.load();
    while (old_value < minValue) {
        // ever update to all_committed_below_index strictly increases it. so this loop will terminate
        if (all_committed_below_index.compare_exchange_weak(old_value, minValue)) {
            break;
        }
    }
}

#endif

MONAD_NAMESPACE_END
