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

void ParallelCommitSystem::reset(txindex_t num_transactions, monad::Address const &beneficiary) {
    this->beneficiary=beneficiary;
    all_committed_below_index.store(0);
    for (txindex_t i = 0; i <= num_transactions; i++) {
        promises[i] = boost::fibers::promise<void>();
    }
      //,pending_footprints_(num_transactions)// not used currently

    // Initialize first transaction as STARTED_UNBLOCKED, rest as STARTED
    if (num_transactions > 0) {
        status_[0].store(TransactionStatus::STARTED_UNBLOCKED);
    }
    else {
        promises[0].set_value();
    }
    for (size_t i = 1; i < num_transactions; i++) {// TODO(aa): delete this loop. do not initialize here. ensure declareFootprint initializes all these, in parallel.
        status_[i].store(TransactionStatus::STARTED);
        footprints_[i]=nullptr;
        nontriv_footprint_contains_beneficiary[i]=false;
    }
    all_done.store(false);
    
}
// pre: footprint has been declared already
const std::set<evmc::address>* ParallelCommitSystem::getFootprint(txindex_t myindex) { return footprints_[myindex]; }

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
    if(footprint && footprint->find(beneficiary)!=footprint->end()){
        nontriv_footprint_contains_beneficiary[myindex]=true;
        //LOG_INFO("declareFootprint: nontriv_footprint_contains_beneficiary[{}] set to true", myindex);
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
        status_[myindex].store(TransactionStatus::FOOTPRINT_COMPUTED_UNBLOCKED);
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
        if(nontriv_footprint_contains_beneficiary[index]) {
            return false;// above, we observed that the previous transacton hasn't committed yet. this transaction may read the exact beneficiary balance, so we need to wait for all previous transactions to commit so that the rewards get finalized.
        }
        unblockTransaction(status, index);
        return true;
    }
    return false;
}

bool ParallelCommitSystem::existsBlockerBefore(txindex_t index) {
    auto committed_ub = all_committed_below_index.load();// transactiosn before this index cannot be blockers
    txindex_t i=committed_ub;
    while(i < index) {
        if (blocksAllLaterTransactions(i)) {
            return true;
        }
        ++i;
        i=std::max(i, all_committed_below_index.load());
    }
    return false;
}

bool ParallelCommitSystem::blocksAllLaterTransactions(txindex_t index) {
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
    //auto status = status_[myindex].load();
    //std::cout << "notifyDone: status of " << myindex << " is " << status_to_string(status) << std::endl;
    // assert(status == TransactionStatus::COMMITTING);
    status_[myindex].store(TransactionStatus::COMMITTED);
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
    bool changed=false;
    auto newUb = all_committed_below_index.load();
    while (newUb< num_transactions) {
        if (status_[newUb].load() != TransactionStatus::COMMITTED) {
            break;
        }
        newUb++;
        changed=true;
    }
    if(!changed) {
        return;
    }
    bool ichanged=advanceLastCommittedUb(newUb);
    if(ichanged && newUb == num_transactions) {
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
 *  steps to debug:
 * 0) check the meaning of wrong merkle root error. does it indicate a problem of the execition of the last block or n-2th block? can test it by instrumenting the execution to do something wrong based on block number.
 * 1) run with valgrind
 * 2) implement change_within_footprint
 * 3) if change_within_footpring asserts are not violated, then only 2 possibilities: 1) BlockState::merge cannot be run concurrently even for disjoing footprints, 2) there is some catastrophic memory corruption in ParallelCommitSystem. debug it
 * 4) to confirm 3.1 (blockstate::merge), in the main branch, insert minimal code to drop promises.wait for blocks whose transactions are completely disjoint. run many times until that block. block 47219 is an example (see below)
 * 5) if 3.1 is not confirmed, investigate 3.2 (memory corruption in ParallelCommitSystem). else tweak BlockState so that merge and car_merge can be run more concurrently
 * 
 * 
 * 2024-12-24 23:22:06.177577979 [1085296] execute_block.cpp:208 LOG_INFO	block number: 47219
2024-12-24 23:22:06.177685659 [1085296] execute_block.cpp:212 LOG_INFO	sender[0]: 0xe6a7a1d47ff21b6321162aea7c6cb457d5476bca
2024-12-24 23:22:06.177688239 [1085296] execute_block.cpp:212 LOG_INFO	sender[1]: 0xf9a19aea1193d9b9e4ef2f5b8c9ec8df93a22356
2024-12-24 23:22:06.177908411 [1085306] parallel_commit_system.cpp:99 LOG_INFO	declareFootprint: status[1] changed from STARTED to FOOTPRINT_COMPUTED
2024-12-24 23:22:06.177915781 [1085306] execute_block.cpp:168 LOG_INFO	footprint[1]: 0x32be343b94f860124dc4fee278fdcbd38c102d88, 0xf9a19aea1193d9b9e4ef2f5b8c9ec8df93a22356,
2024-12-24 23:22:06.177939611 [1085306] parallel_commit_system.cpp:99 LOG_INFO	declareFootprint: status[0] changed from STARTED_UNBLOCKED to FOOTPRINT_COMPUTED_UNBLOCKED
2024-12-24 23:22:06.177943681 [1085306] parallel_commit_system.cpp:182 LOG_INFO	indicesAccessingAddress[0x32be343b94f860124dc4fee278fdcbd38c102d88]: 1,
2024-12-24 23:22:06.177946581 [1085306] parallel_commit_system.cpp:182 LOG_INFO	indicesAccessingAddress[0xf9a19aea1193d9b9e4ef2f5b8c9ec8df93a22356]: 1,
2024-12-24 23:22:06.177947161 [1085306] parallel_commit_system.cpp:162 LOG_INFO	unblockTransaction: status[1] changed from FOOTPRINT_COMPUTED to FOOTPRINT_COMPUTED_UNBLOCKED
2024-12-24 23:22:06.177951761 [1085306] execute_block.cpp:168 LOG_INFO	footprint[0]: 0xe25e3a1947405a1f82dd8e3048a9ca471dc782e1, 0xe6a7a1d47ff21b6321162aea7c6cb457d5476bca,
2024-12-24 23:22:06.179921012 [1085296] ethereum_mainnet.cpp:104 LOG_ERROR	Block: 47219, Computed State Root: 0x80b2ce33f14791b03d34ea19000059aa7a6215d2757ddca392273cf26bf9196f, Expected State Root: 0x05a16e52dbacec805dc881439ef54338e8324ee133a4dbbb8ab17f8c73290054
2024-12-24 23:22:06.182764379 [1085296] monad.cpp:685 LOG_ERROR	block 47219 failed with: wrong merkle root
[Thread 0x7fffed6006c0 (LWP 1085308) exited]
[Thread 0x7fffee0006c0 (LWP 1085307) exited]
[Thread 0x7fffeea006c0 (LWP 1085306) exited]
[Thread 0x7fffef4006c0 (LWP 1085305) exited]
[Thread 0x7ffff6a006c0 (LWP 1085302) exited]
[Thread 0x7ffff74006c0 (LWP 1085301) exited]
[Inferior 1 (process 1085296) exited with code 01]


it seems the issue is that I forgot to take into account that ever transacton implicity updates the balance 
of the block miner's designated beneficiary account by adding a reward to it.
the current handling of it would require adding beneeficiary to every footprint and thus completely spoil any parallelism.
So, we need to do a special case handling of it.
We can add the following array to  BlockState:
beneficiary_balance_deltas_[transactions.size ()].
beneficiary_balance_deltas_[i] can only be updated by the transaction i: BlockState:merge will just set this field.
But it can be read by any transaction. 
It will only be ready by transactions that explicitly access the beneficiary account, e.g. if the beneficiary
account is a contract and the code calls SELFBALANCE.

`ParalllelCommitSystem` will work mostly the same. beneficially account will not be added to footprints unless
they are explicitly accessed by the transaction. waitForPrevTransactions[i] will change as follows in case
the transactiion i explicitly accesses the beneficiary account:
wait for all transactions before i to commit.


BlockState::can_merge will change to add up the array of deltas until the index in places where it reads the beneficiary account.



TODO(aa):
- handle CREATE2: if a footprint has an account not seen before, set the footprint to INF: the account could be a concract which can call anything.
- expand callee prediction to expressions. first add CALLDATA(const)/SENDER/COINBASE. then add binops over them, and maybe CALLDATA(*) 

 *  */
