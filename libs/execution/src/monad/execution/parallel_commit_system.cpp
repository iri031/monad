#include <monad/execution/parallel_commit_system.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/fmt/address_fmt.hpp>


MONAD_NAMESPACE_BEGIN



void ParallelCommitSystem::earlyDestructFibers() {
    for (size_t i = 0; i < MAX_TRANSACTIONS; i++) {
        promises[i] = boost::fibers::promise<void>();
    }
}

void ParallelCommitSystem::reset(txindex_t num_transactions_, monad::Address const &beneficiary) {
    assert(num_transactions_<=MAX_TRANSACTIONS);
    this->num_transactions=num_transactions_;
    this->beneficiary=beneficiary;
    all_committed_below_index.store(0);
    transactions_accessing_address_.clear();
    promises[num_transactions]=boost::fibers::promise<void>();

    if (num_transactions == 0)
        promises[0].set_value();
    all_done.store(false);
    
}
// pre: footprint has been declared already
const std::set<evmc::address>* ParallelCommitSystem::getFootprint(txindex_t myindex) { return footprints_[myindex]; }

void ParallelCommitSystem::registerAddressAccessedBy(const evmc::address& addr, txindex_t index) {
    auto it = transactions_accessing_address_.find(addr);
    if (it == transactions_accessing_address_.end()) {
        it = transactions_accessing_address_.insert({addr, StaticBitset<MAX_TRANSACTIONS>()}).first;
    }
    it->second.setBit(index);
}

void ParallelCommitSystem::compileFootprint() {
    inf_footprint_txs.reset();
    for (txindex_t myindex = 0; myindex < num_transactions; ++myindex) {
        auto footprint = footprints_[myindex];
        if (footprint) {
            for (const auto& addr : *footprint) {
                registerAddressAccessedBy(addr, myindex);
            }
        }
        else {
            inf_footprint_txs.setBit(myindex);
        }
    }
}



void ParallelCommitSystem::declareFootprint(txindex_t myindex, const std::set<evmc::address> *footprint) {
    delete footprints_[myindex];
    footprints_[myindex] = footprint;
    if(footprint && footprint->find(beneficiary)!=footprint->end()){
        nontriv_footprint_contains_beneficiary[myindex]=true;
        //LOG_INFO("footprint[{}] contains beneficiary", myindex);
    }
    else {
        nontriv_footprint_contains_beneficiary[myindex]=false;
    }

    promises[myindex] = boost::fibers::promise<void>();


    if (myindex==0) {
        status_[myindex].store(TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);
    }
    else {
        status_[myindex].store(TransactionStatus::FOOTPRINT_COMPUTED);
    }
    /*
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
        status_[myindex].store(TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);
        //LOG_INFO("declareFootprint: status[{}] changed from STARTED_UNBLOCKED to FOOTPRINT_COMPUTED_UNBLOCKED", myindex);
    } */
    // else {
    //     //LOG_INFO("declareFootprint: status[{}] changed from {} to {}", 
    //     //    myindex, 
    //     //    status_to_string(current_status), 
    //     //    status_to_string(new_status));
    // }

    // if (!existsBlockerBefore(myindex)) {
    //     tryUnblockTransactionsStartingFrom(myindex);
    // }
}

ParallelCommitSystem::~ParallelCommitSystem() {
    // Clean up the footprints (we own these pointers)
    //for (auto footprint : footprints_) {
        //delete footprint;// only delete till num_transactions
    //}
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
    return status > TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS || status == TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
}

void ParallelCommitSystem::unblockTransaction(TransactionStatus status, txindex_t index) {
    while (!isUnblocked(status)) {
        TransactionStatus new_status{TransactionStatus::FOOTPRINT_COMPUTED};// dummy value to get the compiler to shut up about uninitialized new_status
        if (status == TransactionStatus::FOOTPRINT_COMPUTED) {
            new_status = TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED;
        } else if (status == TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS) {
            new_status = TransactionStatus::COMMITTING;
        } else {
            assert(false);
        }

        if (status_[index].compare_exchange_strong(status, new_status)) {
            //LOG_INFO("unblockTransaction: status[{}] changed from {} to {}", 
            //    index, 
            //    status_to_string(status), 
            //    status_to_string(new_status));
            if (new_status == TransactionStatus::COMMITTING) {
                promises[index].set_value();
            }
            break;
        }
        // state[index] only transsitions to a strictly higher value. every CAS fail means some other thread did a transition to a higher value. 
        // the increaments can only happen until COMITTED in the worst case, by which time the loop will terminate (isUnblocked(Comitted)=true).
    }
}

/* return the highest element in the range [ge, lt) in the set s. if no such element exists, return max*/
uint64_t highestElemInRange(const std::set<uint64_t>& s, uint64_t ge, uint64_t lt)
{
    // If set is empty, no valid element.
    if (s.empty()) {
        return std::numeric_limits<uint64_t>::max();  // or another sentinel
    }

    // 1) We want x < lt.
    //    lower_bound(lt) returns an iterator pointing to the first element >= lt.
    //    So if we step one iterator back, that element is guaranteed to be < lt.
    auto it = s.lower_bound(lt);

    // 2) If it == s.begin(), then every element in the set is >= lt,
    //    so we have no element < lt.
    if (it == s.begin()) {
        return std::numeric_limits<uint64_t>::max();
    }

    // 3) Move one step back to get the largest element < lt.
    --it;

    // 4) Check if that element is also >= ge. If yes, it's in [ge, lt).
    if (*it >= ge) {
        return *it; 
    }

    return std::numeric_limits<uint64_t>::max();
}

ParallelCommitSystem::txindex_t ParallelCommitSystem::highestLowerUncommittedIndexAccessingAddress(txindex_t index, const evmc::address& addr) {
    auto it = transactions_accessing_address_.find(addr);
    if (it == transactions_accessing_address_.end()) {
        return std::numeric_limits<txindex_t>::max();
    }
    auto & set = it->second;
    /*LOG_INFO("indicesAccessingAddress[{}]: {}", 
        fmt::format("{}", addr),
        [&set]() {
            std::string result;
            for (auto const &i : *set) {
                result += std::to_string(i) + ", ";
            }
            return result;
        }()); */
    
    // Start from all_committed_below_index instead of set->begin()
    auto committed_ub = all_committed_below_index.load();
    auto result = set.findLargestSetBitInRange(committed_ub, index);
    //LOG_INFO("highestLowerUncommittedIndexAccessingAddress: {} in ({}, {}) for set {}", result, committed_ub, index, set);
    return result;
}

//pre: blocksAllLaterTransactions(i) is false for all i<index
// returns true iff this transaction blocks all later transactions
bool ParallelCommitSystem::tryUnblockTransaction(txindex_t all_committed_ub_, txindex_t index) {
    auto footprint = footprints_[index];
    auto status = status_[index].load();
    bool blocks_all_later_transactions = status != TransactionStatus::COMMITTED && footprint == nullptr;
    if (index==all_committed_ub_) { // index-1<all_committed_ub_ <-> index -1 + 1<=all_committed_ub_ <-> index<=all_committed_ub_ <-> (index == all_committed_ub_ || index < all_committed_ub_). in the latter case, the transaction at index has already commited so we do not need to unblock it. so we can drop the last disjunct.

        unblockTransaction(status, index);
        return blocks_all_later_transactions;
    }
    if (isUnblocked(status)) {
        return blocks_all_later_transactions;
    }

    if (status == TransactionStatus::FOOTPRINT_COMPUTED || status==TransactionStatus::WAITING_FOR_PREV_TRANSACTIONS) {
        if(footprint == nullptr || nontriv_footprint_contains_beneficiary[index]) {
            return blocks_all_later_transactions;
        }
        for (const auto& addr : *footprint) {
            auto highest_prev = highestLowerUncommittedIndexAccessingAddress(index, addr);
            assert(highest_prev<index || highest_prev == std::numeric_limits<txindex_t>::max());
            if (highest_prev != std::numeric_limits<txindex_t>::max() && status_[highest_prev].load() != TransactionStatus::COMMITTED)
                return blocks_all_later_transactions;
        }
        unblockTransaction(status, index);
        return blocks_all_later_transactions;
    }
    return blocks_all_later_transactions;
}

inline bool ParallelCommitSystem::existsBlockerBefore(txindex_t all_committed_ub, txindex_t index) const {
    return (inf_footprint_txs.findLargestSetBitInRange(all_committed_ub, index) != std::numeric_limits<txindex_t>::max());
}

// inline bool ParallelCommitSystem::blocksAllLaterTransactions(txindex_t index) const {
//     assert(index<num_transactions);
//     auto status = status_[index].load();
//     if (footprints_[index] == nullptr /* INF footprint */ && status != TransactionStatus::COMMITTED) {
//         return true;
//     }
//     return false;
// }

void ParallelCommitSystem::waitForAllTransactionsToCommit() {
    promises[num_transactions].get_future().wait();
}

//pre: blocksAllLaterTransactions(i) is false for all i<start
void ParallelCommitSystem::tryUnblockTransactionsStartingFrom(txindex_t all_committed_ub, txindex_t start) {

    // unblock or wake up later transactions
    // once we hit a transaction whose footprint is not yet computed,
    // we cannot wake up or unblock transactions after that transaction
    // every transaction accesses at least 1 account and the uncomputed footprint may include that account.
    txindex_t index=start;
    index=std::max(index, all_committed_ub);
    while(index < num_transactions) {
        bool blocks_all_later_transactions = tryUnblockTransaction(all_committed_ub, index);
        if (blocks_all_later_transactions) {
            break;
        }
        ++index;
        all_committed_ub = all_committed_below_index.load();
        index=std::max(index, all_committed_ub);
    }
}

std::string ParallelCommitSystem::status_to_string(TransactionStatus status) {
    switch (status) {
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
    bool alldone = false;
    //LOG_INFO("notifyDone: status[{}] changed from {} to {}", myindex, status_to_string(TransactionStatus::COMMITTING), status_to_string(TransactionStatus::COMMITTED));
    auto new_all_committed_ub = updateLastCommittedUb(alldone);
    if(alldone) {// there is currently a rare bug here. this object may have been deallocated by now. using shared_ptr can fix. static allocation of this object may be better if we can compute a not-too-loose bound on #transactions.
        return;
    }
    if (!existsBlockerBefore(new_all_committed_ub, myindex)) {
        tryUnblockTransactionsStartingFrom(new_all_committed_ub, myindex+1); // unlike before, the transaction myindex+1 cannot necesssarily be unblocked here because some transaction before myindex may not have committed and may have conflicts
    }
}

void ParallelCommitSystem::notifyAllDone() {
    bool old_value = false;
    if (all_done.compare_exchange_strong(old_value, true)) {
        promises[num_transactions].set_value();
    }
}

ParallelCommitSystem::txindex_t ParallelCommitSystem::updateLastCommittedUb(bool & alldone) {
//    bool changed=false;
    auto newUb = all_committed_below_index.load();
    while (newUb< num_transactions) {
        if (status_[newUb].load() != TransactionStatus::COMMITTED) {
            break;
        }
        newUb++;
        //changed=true;
    }
    // if(!changed) {
    //     return;
    // }
    auto new_all_committed_ub = advanceLastCommittedUb(newUb);// it may return a value strictly greater than newUb
    if(new_all_committed_ub == num_transactions) {
        alldone = true;
        notifyAllDone(); // one problem is that this unblocks execute_block, which can destruct the this object, even though more calls are done on it, e.g. in notifyDone
    }
    return new_all_committed_ub;
}

ParallelCommitSystem::txindex_t ParallelCommitSystem::advanceLastCommittedUb(txindex_t minValue) {
    txindex_t old_value = all_committed_below_index.load();
    while (old_value < minValue) {
        // every update to all_committed_below_index strictly increases it. so this loop will terminate
        if (all_committed_below_index.compare_exchange_strong(old_value, minValue)) {
            return minValue;
        }
    }
    return old_value;
}

MONAD_NAMESPACE_END

/**
 
TODO(aa):
- check how the priority pool works. if transactions 2,4-45 are running and 3 becomes ready, will it run before 46? 3 should run to get full advantage and reduce retries.
- use a concurrent min heap to implement existsBlockerBefore in O(1), currently it is O(n)
- delay the transfer transactions based on footprint
- expand callee prediction to expressions. first add CALLDATA(const)/SENDER/COINBASE. then add binops over them, and maybe CALLDATA(*) 

 *  */
