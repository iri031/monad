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
std::set<evmc::address> *ParallelCommitSystem::getFootprint(txindex_t myindex) { return nullptr; }
#else

void ParallelCommitSystem::reset(txindex_t num_transactions_, monad::Address const &beneficiary) {
    assert(num_transactions_<=MAX_TRANSACTIONS);
    this->num_transactions=num_transactions_;
    this->beneficiary=beneficiary;
    uncommited_transactions_with_inf_footprint.reset();
    all_committed_below_index.store(0);
    for (auto& pair : transactions_accessing_address_) {
          delete pair.second; // matches the "new tbb::concurrent_set<txindex_t>()" in registerAddressAccessedBy
    }
    transactions_accessing_address_.clear();
    for (size_t i = 0; i < num_transactions; i++) {// TODO(aa): do not initialize here, except promises. ensure declareFootprint initializes all these, in parallel.
        promises[i] = boost::fibers::promise<void>();
    }
    promises[num_transactions]=boost::fibers::promise<void>();

    if (num_transactions == 0)
        promises[0].set_value();
    all_done.store(false);
    
}
// pre: footprint has been declared already
const std::set<evmc::address>* ParallelCommitSystem::getFootprint(txindex_t myindex) { return footprints_[myindex]; }

void ParallelCommitSystem::registerAddressAccessedBy(const evmc::address& addr, txindex_t index) {
    ConcurrentTxSet * set;
    {
        auto it = transactions_accessing_address_.find(addr);
        if (it == transactions_accessing_address_.end()) {
            it = transactions_accessing_address_.insert({addr, new ConcurrentTxSet()}).first;
        }
        set=it->second;
    }
    // because nobody will ever change the set pointer in the map, we do set->insert after `it` goes out of scope, 
    // thus releasing the lock, and allowing other threads to concurrently insert into the set.
    // if this address was not in the map before, `it` may hold a write lock on the set, thus preventing other threads from accessing the set.
    set->set_bit_without_index_upddate(index);
}

void ParallelCommitSystem::unregisterAddressAccessedBy(const evmc::address& addr, txindex_t index) {
    auto it = transactions_accessing_address_.find(addr);
    if (it != transactions_accessing_address_.end()) {
        it->second->unset_bit_update_index(index);
    }
}

void ParallelCommitSystem::declareFootprint(txindex_t myindex, const std::set<evmc::address> *footprint) {
    delete footprints_[myindex];
    footprints_[myindex] = footprint;
    if (footprint) {
        for (const auto& addr : *footprint) {
            registerAddressAccessedBy(addr, myindex);
        }
    }
    else {
        uncommited_transactions_with_inf_footprint.set_bit_without_index_upddate(myindex);
    }
    if(footprint && footprint->find(beneficiary)!=footprint->end()){
        nontriv_footprint_contains_beneficiary[myindex]=true;
        //LOG_INFO("footprint[{}] contains beneficiary", myindex);
    }
    else {
        nontriv_footprint_contains_beneficiary[myindex]=false;
    }


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

bool ParallelCommitSystem::existsPrevUncommittedNonInfFootprintTxAccessingAddress(txindex_t index, const evmc::address& addr) {
    auto it = transactions_accessing_address_.find(addr);
    if (it == transactions_accessing_address_.end()) {
        return false;// no transaction in this block with non-INF footprint accesses this address
    }
    auto set = it->second;
    return set->contains_any_element_lessthan(index);
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
        if(nontriv_footprint_contains_beneficiary[index]) {
            return false;// above, we observed that the previous transacton hasn't committed yet. this transaction may read the exact beneficiary balance, so we need to wait for all previous transactions to commit so that the rewards get finalized.
        }
        for (const auto& addr : *footprint) {
            if (existsPrevUncommittedNonInfFootprintTxAccessingAddress(index, addr)) {
                return false;// this may be a spurious false positive in case of a race, but we have other mechanisms to ensure every transaction is eventually unblocked.
            }
        }
        unblockTransaction(status, index);
        return true;
    }
    return false;
}

bool ParallelCommitSystem::existsBlockerBefore(txindex_t index) const {
    return uncommited_transactions_with_inf_footprint.contains_any_element_lessthan(index);
    // this assumes that all footprints are declared before starting any transaction.
    // but if we need to compute footprints lazily, we can fix that by having the ConcurrentTxSet constructor create an all 1 bitset  and then unset bits when a transaction declares a non-INF footprint.

}

bool ParallelCommitSystem::blocksAllLaterTransactions(txindex_t index) const {
    assert(index<num_transactions);
    auto status = status_[index].load();
    if (status == TransactionStatus::STARTED || status == TransactionStatus::STARTED_UNBLOCKED) {
        return true;
    }
    if (footprints_[index] == nullptr /* INF footprint */ && status != TransactionStatus::COMMITTED) {
        return true;
    }
    return false;
}

void ParallelCommitSystem::waitForAllTransactionsToCommit() {
    promises[num_transactions].get_future().wait();
}

//pre: blocksAllLaterTransactions(i) is false for all i<start
void ParallelCommitSystem::tryUnblockTransactionsStartingFrom(txindex_t start) {

    // unblock or wake up later transactions
    // once we hit a transaction whose footprint is not yet computed,
    // we cannot wake up or unblock transactions after that transaction
    // every transaction accesses at least 1 account and the uncomputed footprint may include that account.
    txindex_t index=start;
    index=std::max(index, all_committed_below_index.load());
    while(index < num_transactions) {
        auto current_status = status_[index].load();
        tryUnblockTransaction(current_status, index);
        if (blocksAllLaterTransactions(index)) {
            break;
        }
        ++index;
        index=std::max(index, all_committed_below_index.load());
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
    auto status = status_[myindex].load();
    //std::cout << "notifyDone: status of " << myindex << " is " << status_to_string(status) << std::endl;
    assert(status == TransactionStatus::COMMITTING);
    status_[myindex].store(TransactionStatus::COMMITTED);
    uncommited_transactions_with_inf_footprint.unset_bit_update_index(myindex);
    if(footprints_[myindex]) {
        for(auto addr: *footprints_[myindex]) {
            unregisterAddressAccessedBy(addr, myindex);
        }
    }
    LOG_INFO("notifyDone: status[{}] changed from {} to {}", myindex, status_to_string(TransactionStatus::COMMITTING), status_to_string(TransactionStatus::COMMITTED));
    updateLastCommittedUb();
    if(all_done.load()) {// there is currently a rare bug here. this object may have been deallocated by now. using shared_ptr can fix. static allocation of this object may be better if we can compute a not-too-loose bound on #transactions.
        return;
    }
    if (!existsBlockerBefore(myindex)) {
        tryUnblockTransactionsStartingFrom(myindex+1); // unlike before, the transaction myindex+1 cannot necesssarily be unblocked here because some transaction before myindex may not have committed and may have conflicts
    }
}

void ParallelCommitSystem::notifyAllDone() {
    bool old_value = false;
    if (all_done.compare_exchange_strong(old_value, true)) {
        promises[num_transactions].set_value();
    }
}

void ParallelCommitSystem::updateLastCommittedUb() {
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
    advanceLastCommittedUb(newUb);
    if(newUb == num_transactions) {
        notifyAllDone(); // one problem is that this unblocks execute_block, which can destruct the this object, even though more calls are done on it, e.g. in notifyDone
    }
}

bool ParallelCommitSystem::advanceLastCommittedUb(txindex_t minValue) {
    txindex_t old_value = all_committed_below_index.load();
    while (old_value < minValue) {
        // ever update to all_committed_below_index strictly increases it. so this loop will terminate
        if (all_committed_below_index.compare_exchange_weak(old_value, minValue)) {
            return true;
        }
    }
    return false;
}

#endif

MONAD_NAMESPACE_END

/**
 * 
The Coq proof will guarantee correctness but will not prove that every transaction is eventually unblocked. 
Sketch for why every transaction is eventually unblocked (assuming evmone eventually terminates):
Proof by natural unduction on transaction index..
- base case: index=0. 0 is unblocked by the reset function called in execute_block.
- inductive step: assume every transaction with index i or below will eventually be unblocked. need to prove that i+1 will be unblocked eventually.
   let j <=i be the transaction that last changes its status to COMMITTED in notifyDone. 
   on x86, we have a total store order, so there is a unique such transaction.
   after that notifyDone will call updateLastCommittedUb, which must see that all transactions with index i or below are COMMITTED. 
   so it must set all_committed_below_index to i+1. then, that notifyDone will call
    tryUnblockTransactionsStartingFrom(i+1) will unblock i+1 when it sees that all_committed_below_index is i+1.
   this will up the promise and wake up i+1 if it was waiting.
Qed.



 
TODO(aa):
- check how the priority pool works. if transactions 2,4-45 are running and 3 becomes ready, will it run before 46? 3 should run to get full advantage and reduce retries.
- use a concurrent min heap to implement existsBlockerBefore in O(1), currently it is O(n). a new field, uncommited_transactions_with_INF_footprint will be added. also use it in transactions_accessing_address_ and highestLowerUncommittedIndexAccessingAddress. 
    notifyDone will then need to delete itself from the heap for all addresses in its footprint. also, if the footprint is null, also delete itself from uncommited_transactions_with_INF_footprint.
- delay the transfer transactions based on footprint
- expand compute_footprint in execute_block to support the cases where the preductions were expressions, not just constants. first add support CALLDATA(const)/SENDER/COINBASE. then add binops over them, and maybe CALLDATA(*). 
   need to write a function to interpret callee expressions based on the state accessible in execute_block.

 *  */
