#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/fmt/transaction_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/parallel_commit_system.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

// EIP-4895
constexpr void process_withdrawal(
    State &state, std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    if (withdrawals.has_value()) {
        for (auto const &withdrawal : withdrawals.value()) {
            state.add_to_balance(
                withdrawal.recipient,
                uint256_t{withdrawal.amount} * uint256_t{1'000'000'000u});
        }
    }
}

inline void
transfer_balance_dao(BlockState &block_state, Incarnation const incarnation)
{
    State state{block_state, incarnation};

    for (auto const &addr : dao::child_accounts) {
        auto const balance = intx::be::load<uint256_t>(state.get_balance(addr));
        state.add_to_balance(dao::withdraw_account, balance);
        state.subtract_from_balance(addr, balance);
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);
}

inline void set_beacon_root(BlockState &block_state, Block &block)
{
    constexpr auto BEACON_ROOTS_ADDRESS{
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02_address};
    constexpr uint256_t HISTORY_BUFFER_LENGTH{8191};

    State state{block_state, Incarnation{block.header.number, 0}};
    if (state.account_exists(BEACON_ROOTS_ADDRESS)) {
        uint256_t timestamp{block.header.timestamp};
        bytes32_t k1{
            to_bytes(to_big_endian(timestamp % HISTORY_BUFFER_LENGTH))};
        bytes32_t k2{to_bytes(to_big_endian(
            timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH))};
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k1, to_bytes(to_big_endian(timestamp)));
        state.set_storage(
            BEACON_ROOTS_ADDRESS,
            k2,
            block.header.parent_beacon_block_root.value());

        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
    }
}

#define MAX_FOOTPRINT_SIZE 20

// if this returns true, then the address MUST be a non-contract account. for correctness, it can always return false, but for performance, it should do that only for addresses created in this block.
bool address_known_to_be_non_contract_dell(evmc::address address, BlockState &block_state, CalleePredInfo &) {
    auto const to_account = block_state.read_account(address);
    if(!to_account.has_value()) {// an account that is first seen in this block.

        /* there is no reliable way to determine if this is account is a contract account or not. a previous contract transaction in this block may create a contract at this address. we cannot wait to run to find out. if a static analysis finds that all prev transactions in this block has no CREATE2 opcode THEN we can return true
        if(transaction.data.empty()) {
            return true;// new EOA account creation
        }
        */
        return false;
    }
    return to_account.value().code_hash==NULL_HASH;
}

//this is cheating a tiny bit as it knows more than what we would know in production. 
// specifically, if an address was never seen in previous blocks, it is not known to be a contract account blocks, we cannot know the correct answer here. 
// but because we already have the static analysis of all contracts called beforehand, we are able to look into the future here. 
//the impact of this cheagint should likely be insignificant in tps. 
// the above impl doesnt cleat but it loads the account from DB which is an expensive thing to do to just compute footprints, which is done even before transactions are started
bool address_known_to_be_non_contract(evmc::address address, CalleePredInfo &cinfo) {
    return (cinfo.code_hashes.find(address)==cinfo.code_hashes.end());
}

struct CallChainNode {
    evmc::address callee;
    evmc::address caller;
    bool root_call;

    bool operator<(const CallChainNode& other) const {
        if (callee < other.callee) return true;
        if (callee > other.callee) return false;
        if (caller < other.caller) return true;
        if (caller > other.caller) return false;
        return root_call < other.root_call;
    }
};

/** returns true iff the footprint has been overapproximated to INF. in that case, footprint is deleted 
 * \pre address_known_to_be_non_contract(runningAddress)=false, which means runningAddress has a non-empty code hash or hasnt been seen until this block
*/
bool insert_callees(Block &block, Transaction const &transaction, evmc::address origin, std::set<evmc::address> *footprint, std::vector<CallChainNode> & to_be_explored, std::set<CallChainNode> & seen_nodes, CallChainNode cnode, CalleePredInfo &callee_pred_info) {
    if(footprint->size()>MAX_FOOTPRINT_SIZE) {
        return true;
    }

    auto calles=callee_pred_info.lookup_callee(cnode.callee);
    if(!calles.has_value()) {
        return true;// absense in map means callee prediction failed. the empty callee set is denoted by an empty vector.
    }
    //LOG_INFO("insert_callees: runningAddress: {} has {} callees", runningAddress, calles.value()->callees.size());
    for (uint32_t index : calles.value()->callees) {
        std::optional<Word256> callee_addrp=callee_pred_info.epool.interpretExpression(index, block.header, transaction, cnode.caller, origin, cnode.root_call);
        if(!callee_addrp.has_value()) {
            return true;// not enough information to interpret the callee address expression to a constant, e.g. CALLDATA is currently not available for non-root nodes in callchain. so this callee can be anything: overapproximate this transactions's footprint to INF
        }
        evmc::address callee_addr=get_address(callee_addrp.value());
        footprint->insert(callee_addr);
        CallChainNode seenNode={callee_addr, cnode.callee, false};
        auto res=seen_nodes.insert(seenNode);
        if(address_known_to_be_non_contract(callee_addr, callee_pred_info)) {
            //LOG_INFO("insert_callees: callee_addr: {} is known_to_be_non_contract", callee_addr);
            continue;
        }
        if(res.second) {
            to_be_explored.push_back(seenNode);
        }
    }
    for (uint32_t index : calles.value()->delegateCallees) {
        std::optional<Word256> callee_addrp=callee_pred_info.epool.interpretExpression(index, block.header, transaction, cnode.caller, origin, cnode.root_call);
        if(!callee_addrp.has_value()) {
            return true;// not enough information to interpret the callee address expression to a constant, e.g. CALLDATA is currently not available for non-root nodes in callchain. so this callee can be anything: overapproximate this transactions's footprint to INF
        }
        evmc::address callee_addr=get_address(callee_addrp.value());
        if(address_known_to_be_non_contract(callee_addr, callee_pred_info)) {
            continue;
        }
        CallChainNode seenNode={callee_addr, cnode.callee, false};
        auto res=seen_nodes.insert(seenNode);// we do not insert into footprint, because DELEGATECALL/CALLCODE does not directly change callee's account. we insert it here to avoid infinite loops
        if(res.second) {
            to_be_explored.push_back(seenNode);
        }
    }
    for (uint32_t index : calles.value()->balanceAccounts) {
        std::optional<Word256> balance_addrp=callee_pred_info.epool.interpretExpression(index, block.header, transaction, cnode.caller, origin, cnode.root_call);
        if(!balance_addrp.has_value()) {
            return true;// not enough information to interpret the callee address expression to a constant, e.g. CALLDATA is currently not available for non-root nodes in callchain. so this callee can be anything: overapproximate this transactions's footprint to INF
        }
        evmc::address balance_addr=get_address(balance_addrp.value());
        footprint->insert(balance_addr);
    }
    return false;
}

std::atomic<uint64_t> numTTFp=0;

uint64_t numTTPredictedFootprints() {
    return numTTFp;
}


//std::set<evmc::address> *footprints[MAX_TRANSACTIONS];
// sender address is later added to the footprint by the caller, because sender.nonce is updated by the transaction
// for now, we assume that no transaction calls a contract created by a previous transaction in this very block. need to extend static analysis to look at predicted stacks at CREATE/CREATE2
 std::set<evmc::address> * compute_footprint(Block &block, Transaction const &transaction, evmc::address sender, CalleePredInfo &callee_pred_info, uint64_t /*tx_index*/=0) {
    if(!transaction.to.has_value()) {
        //LOG_INFO("compute_footprint: tx_index: {} has no empty to value", tx_index);
        return nullptr;//this is sound but not optimal for performance. it seems even the init code can call contracts
    }
    evmc::address runningAddress = transaction.to.value();
    std::set<evmc::address> *footprint=new std::set<evmc::address>();
    footprint->insert(runningAddress);
    if(address_known_to_be_non_contract(runningAddress, callee_pred_info)) {
        //numTTFp++;
        //LOG_INFO("compute_footprint: tx_index: {} address_known_to_be_non_contract: {}", tx_index, runningAddress);
        return footprint;
    }
    //LOG_INFO("compute_footprint: tx_index: {} address NOT known_to_be_non_contract: {}", tx_index, runningAddress);

    std::vector<CallChainNode> to_be_explored;
    std::set<CallChainNode> seen_nodes;// seen calle
    to_be_explored.push_back({runningAddress, sender, true});
    bool overapproximated=false;
    while((!overapproximated)&&(to_be_explored.size()>0)) {
        CallChainNode runningAddress=to_be_explored.back();
        to_be_explored.pop_back();
        overapproximated=insert_callees(block, transaction, sender, footprint, to_be_explored, seen_nodes, runningAddress, callee_pred_info);
    }
    if(overapproximated) {
        delete footprint;
        return nullptr;
    }
    return footprint;
}

void insert_to_footprint(std::set<evmc::address> *footprint, evmc::address address) {
    if(footprint==nullptr) {
        return; // footprint is INF, so the address is already a part of it
    }
    footprint->insert(address);
}

void print_footprint(std::set<evmc::address> *footprint, uint64_t index) {
    if(footprint==nullptr) {
        LOG_INFO("footprint[{}]: INF", index);
        return;
    }
    std::string footprint_str = "";
    for(auto const &addr: *footprint) {
        footprint_str += fmt::format("{}, ", addr);
    }
    LOG_INFO("footprint[{}]: {}", index, footprint_str);
}

std::atomic<uint64_t> numPredFootprints=0;
uint64_t numPredictedFootprints() {
    return numPredFootprints.load();
}

std::chrono::duration<double> compile_footprints_time{0};
std::chrono::duration<double> footprint_time{0};
std::chrono::duration<double> get_compile_footprints_time() {
    return compile_footprints_time;
}
std::chrono::duration<double> get_footprint_time() {
    return footprint_time;
}
IdealFP ideal_fp;
IdealFP & getIdealFP() {
    return ideal_fp;
}
uint64_t startBlockNumber;
std::vector<std::set<evmc::address>> & blockFootprint(uint64_t blockNumber) {
    return getIdealFP()[blockNumber-startBlockNumber];
}

void setStartBlockNumber(uint64_t startBlockNumber) {
    startBlockNumber = startBlockNumber;
}

std::chrono::duration<double> compute_footprints_time[MAX_TRANSACTIONS];
ParallelCommitSystem parallel_commit_system;
template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &chain, Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, CalleePredInfo &callee_pred_info)
{
    TRACE_BLOCK_EVENT(StartBlock);
    block_state.init(block.header.beneficiary, block.transactions.size());

    if constexpr (rev >= EVMC_CANCUN) {
        set_beacon_root(block_state, block);
    }

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(
                block_state, Incarnation{block.header.number, 0});
        }
    }

    std::shared_ptr<std::optional<Address>[]> const senders{
        new std::optional<Address>[block.transactions.size()]};

    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[block.transactions.size()]};
    uint64_t num_transactions = block.transactions.size();
    blockFootprint(block.header.number).reserve(block.transactions.size());

//    LOG_INFO("block number: {}", block.header.number);
    parallel_commit_system.reset(block.transactions.size(), block.header.beneficiary);
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i = i,
             senders = senders,
             promises = promises,
             &callee_pred_info = callee_pred_info,
             &priority_pool,
             &block,
             &block_state,
             num_transactions,
             &transaction = block.transactions[i]] {
                //auto start_time = std::chrono::high_resolution_clock::now();
                senders[i] = recover_sender(transaction);
                //std::this_thread::sleep_for(std::chrono::milliseconds(1000));
                std::set<evmc::address> *footprint=compute_footprint(block, transaction, senders[i].value(), callee_pred_info, i);
                insert_to_footprint(footprint, senders[i].value());
                // if(footprint) {
                //     for(auto const &addr: *footprint) {
                //         priority_pool.submit(0, [&addr, i=i, &block_state] {
                //                 block_state.cache_account(addr);
                //         });
                //     }
                // }
                if(footprint!=nullptr) {
                    numPredFootprints++;
                }

                parallel_commit_system.declareFootprint(i, footprint);
                //auto end_time = std::chrono::high_resolution_clock::now();
                //std::chrono::duration<double> elapsed_seconds = end_time - start_time;
                //compute_footprints_time[i] = elapsed_seconds;
                //print_footprint(footprint, i);
                promises[i].set_value();
            });
    }
    block_state.load_preblock_beneficiary_balance();


    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        promises[i].get_future().wait();
        //LOG_INFO("sender[{}]: {}", i, fmt::format("{}", senders[i].value()));
    }
    
    {
        //auto start_time = std::chrono::high_resolution_clock::now();
        parallel_commit_system.compileFootprints();
        //auto end_time = std::chrono::high_resolution_clock::now();
        //std::chrono::duration<double> elapsed_seconds = end_time - start_time;
        //compile_footprints_time += elapsed_seconds;
        //for(unsigned i = 0; i < num_transactions; ++i) {
        //    footprint_time += compute_footprints_time[i];
        //}
        //footprint_time += elapsed_seconds;
    }
    
    std::shared_ptr<std::optional<Result<ExecutionResult>>[]> const results{
        new std::optional<Result<ExecutionResult>>[block.transactions.size()]};



    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            num_transactions+i,
            [&chain = chain,
             i = i,
             results = results,
             &transaction = block.transactions[i],
             &parallel_commit_system = parallel_commit_system,
             &sender = senders[i],
             &header = block.header,
             &block_hash_buffer = block_hash_buffer,
             &block_state, &callee_pred_info] {
                results[i] = execute<rev>(
                    chain,
                    i,
                    transaction,
                    sender,
                    header,
                    block_hash_buffer,
                    block_state,
                    parallel_commit_system);
                parallel_commit_system.notifyDone(i);
            });
    }

    parallel_commit_system.waitForAllTransactionsToCommit();

    std::vector<ExecutionResult> retvals;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_UNLIKELY(results[i].value().has_error())) {
            LOG_ERROR(
                "tx {} {} validation failed: {}",
                i,
                block.transactions[i],
                results[i].value().assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto retval, std::move(results[i].value()));
        retvals.push_back(std::move(retval));
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &[receipt, call_frame] : retvals) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (rev >= EVMC_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    apply_block_reward<rev>(state, block);

    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    return retvals;
}

EXPLICIT_EVMC_REVISION(execute_block);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &chain, evmc_revision const rev, Block &block,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, CalleePredInfo &callee_pred_info)
{
    SWITCH_EVMC_REVISION(
        execute_block,
        chain,
        block,
        block_state,
        block_hash_buffer,
        priority_pool, callee_pred_info);
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
