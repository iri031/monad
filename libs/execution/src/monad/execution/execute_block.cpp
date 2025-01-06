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

#define MAX_FOOTPRINT_SIZE 10

// if this returns true, then the address MUST be a non-contract account. for correctness, it can always return false, but for performance, it should do that only for addresses created in this block.
bool address_known_to_be_non_contract(BlockState &block_state, evmc::address address) {
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

/** returns true iff the footprint has been overapproximated to INF. in that case, footprint is deleted 
 * \pre address_known_to_be_non_contract(runningAddress)=false, which means runningAddress has a non-empty code hash or hasnt been seen until this block
*/
bool insert_callees(BlockState &block_state, std::set<evmc::address> *footprint, std::vector<evmc::address> & to_be_explored, std::set<evmc::address> & seen_delegate_callees, evmc::address runningAddress, CalleePredInfo &callee_pred_info) {
    if(footprint->size()>MAX_FOOTPRINT_SIZE) {
        delete footprint;
        return true;
    }

    auto calles=callee_pred_info.lookup_callee(runningAddress);
    if(!calles.has_value()) {
        return true;// absense in map means callee prediction failed. the empty callee set is denoted by an empty vector.
    }
    for (uint32_t index : calles.value()->callees) {
        evmc::address callee_addr=get_address(index, callee_pred_info.epool);
        if(address_known_to_be_non_contract(block_state, callee_addr)) {
            continue;
        }
        auto res=footprint->insert(callee_addr);
        if(res.second) {
            to_be_explored.push_back(callee_addr);
        }
    }
    for (uint32_t index : calles.value()->delegateCallees) {
        evmc::address callee_addr=get_address(index, callee_pred_info.epool);
        if(address_known_to_be_non_contract(block_state, callee_addr)) {
            continue;
        }
        if (footprint->find(callee_addr)!=footprint->end()) {// this was already insested to to_be_explored
            continue;
        }
        auto res=seen_delegate_callees.insert(callee_addr);// we do not insert into footprint, because DELEGATECALL/CALLCODE does not directly change callee's account. we insert it here to avoid infinite loops
        if(res.second) {
            to_be_explored.push_back(callee_addr);// the called code, even though it runs in the context of the caller, can do CALL(foo) and then change the account of foo. so we need to recursively analyze callee_addr for CALL
        }
    }
    return false;
}


// sender address is later added to the footprint by the caller, because sender.nonce is updated by the transaction
// for now, we assume that no transaction calls a contract created by a previous transaction in this very block. need to extend static analysis to look at predicted stacks at CREATE/CREATE2
 std::set<evmc::address> * compute_footprint(BlockState &block_state, Transaction const &transaction, CalleePredInfo &callee_pred_info, uint64_t /*tx_index*/=0) {
    if(!transaction.to.has_value()) {
        //LOG_INFO("compute_footprint: tx_index: {} has no empty to value", tx_index);
        return nullptr;//this is sound but not optimal for performance. add a way for the ParallelCommitSystem to  know that this is creating a NEW contract, so that we know that there is no conflict with block-pre-existing contracts
    }
    evmc::address runningAddress = transaction.to.value();
    std::set<evmc::address> *footprint=new std::set<evmc::address>();
    footprint->insert(runningAddress);
    if(address_known_to_be_non_contract(block_state, transaction.to.value())) {
        //LOG_INFO("compute_footprint: tx_index: {} address_known_to_be_non_contract: {}", tx_index, runningAddress);
        return footprint;
    }
    //LOG_INFO("compute_footprint: tx_index: {} address NOT known_to_be_non_contract: {}", tx_index, runningAddress);

    std::vector<evmc::address> to_be_explored;
    std::set<evmc::address> seen_delegate_callees;// a delegate/callcode-only callee is not itself a part of footprint but we look for its CALLees
    to_be_explored.push_back(runningAddress);
    bool overapproximated=false;
    while((!overapproximated)&&(to_be_explored.size()>0)) {
        evmc::address runningAddress=to_be_explored.back();
        to_be_explored.pop_back();
        overapproximated=insert_callees(block_state, footprint, to_be_explored, seen_delegate_callees, runningAddress, callee_pred_info);
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

    parallel_commit_system.reset(block.transactions.size(), block.header.beneficiary);
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i = i,
             senders = senders,
             promises = promises,
             &block_state = block_state,
             &callee_pred_info = callee_pred_info,
             &transaction = block.transactions[i]] {
                senders[i] = recover_sender(transaction);
                #if !SEQUENTIAL
                std::set<evmc::address> *footprint=compute_footprint(block_state, transaction, callee_pred_info, i);
                insert_to_footprint(footprint, senders[i].value());
                parallel_commit_system.declareFootprint(i, footprint);
                //print_footprint(footprint, i);
                #endif
                promises[i].set_value();
            });
    }
    block_state.load_preblock_beneficiary_balance();

    //LOG_INFO("block number: {}, block beneficiary: {}", block.header.number, block.header.beneficiary);

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        promises[i].get_future().wait();
        //LOG_INFO("sender[{}]: {}", i, fmt::format("{}", senders[i].value()));
    }

    std::shared_ptr<std::optional<Result<ExecutionResult>>[]> const results{
        new std::optional<Result<ExecutionResult>>[block.transactions.size()]};



    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
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
