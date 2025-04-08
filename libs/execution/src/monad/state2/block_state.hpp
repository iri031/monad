#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/int_fmt.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>
#include <intx/intx.hpp>
#include <quill/detail/LogMacros.h>
#include <set>
#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;
class BlockState final
{
    Db &db_;
    StateDeltas state_{};
    Code code_{};
    std::vector<std::pair<::intx::uint256,bool>> beneficiary_balance_updates;//bool true represents increment by ith transaction, false represents absolute value at the end of ith transaction
    monad::Address block_beneficiary;
    uint256_t preblock_beneficiary_balance;

public:
    constexpr static bool BENEFICIARY_BALANCE_INCREMENT=true;
    constexpr static bool BENEFICIARY_BALANCE_ABSOLUTE=false;

    const monad::Address& get_block_beneficiary() const{
        return block_beneficiary;
    }
    void init(monad::Address const &beneficiary, uint64_t num_txs){
        block_beneficiary=beneficiary;
        beneficiary_balance_updates.clear();// TODO(aa): preallocate statically
        beneficiary_balance_updates.resize(num_txs,std::make_pair(0,BENEFICIARY_BALANCE_INCREMENT));
    }
    void cache_account(Address const &);

    BlockState(Db &);

    std::optional<Account> read_account(Address const &, const std::optional<uint64_t> & txindex=std::nullopt);

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &key);

    std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &);

    inline uint256_t beneficiary_balance_just_before_tx_index(uint64_t tx_index) const
    {
        uint256_t increments_sum{0};
        // Process transactions in reverse order
        for (int64_t i = tx_index-1; i >= 0; --i) {
            if (beneficiary_balance_updates[i].second==BENEFICIARY_BALANCE_ABSOLUTE) {
                return beneficiary_balance_updates[i].first+increments_sum;
            }
            increments_sum += beneficiary_balance_updates[i].first;
        }
        return preblock_beneficiary_balance+increments_sum;
    }
    inline uint256_t beneficiary_balance_just_after_last_tx() const{
        return beneficiary_balance_just_before_tx_index(beneficiary_balance_updates.size());
    }
    inline bool eq_beneficiary_ac_before_txindex(Account const &other, uint64_t tx_index) const
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_.find(it, block_beneficiary));// TODO: drop?
        assert(it->second.account.second.has_value());
        const monad::Account &beneficiary_account =
            it->second.account.second.value();
        uint256_t beneficiary_balance =
            beneficiary_balance_just_before_tx_index(tx_index);
        if (beneficiary_balance != other.balance) {
            //LOG_INFO("eq_beneficiary_ac_before_txindex {}: beneficiary_balance {} != other.balance {}, preblock_beneficiary_balance {}", tx_index, beneficiary_balance, other.balance, preblock_beneficiary_balance);
            return false;
        }
        return beneficiary_account.equal_except_balance(other);
    }

    bool can_merge_par(State const &, uint64_t tx_index, bool & beneficiary_touched, bool parallel_beneficiary=false);
    inline bool can_merge(State const &state){
        bool beneficiary_touched=false;
        return can_merge_par(state,0,beneficiary_touched,false);
    }

    // block_beneficiary_reward.has_value iff the transaction only changed the beneficiary's balance by adding the fee reward
    void merge_par(State const &, uint64_t tx_index, std::optional<uint256_t> block_beneficiary_reward, bool parallel_beneficiary=false);
    inline void merge(State const & state){
        merge_par(state,0,std::nullopt,false);
    }
    bool assumptions_within_footprint(State const &state, const std::set<evmc::address>*footprint, uint64_t tx_index);

    void update_beneficiary_delta(uint64_t tx_index, intx::uint256 delta);

    //must be called before any transaction calls can_merge
    inline void load_preblock_beneficiary_balance(){
        auto const beneficiary_account = read_account(block_beneficiary, std::nullopt);
        //assert(beneficiary_account.has_value());
        if(beneficiary_account.has_value()){
            preblock_beneficiary_balance=beneficiary_account.value().balance;
        }
        else{
            preblock_beneficiary_balance=0;
        }
    }

    // TODO: remove round_number parameter, retrieve it from header instead once
    // we add the monad fields in BlockHeader
    void commit(
        BlockHeader const &, std::vector<Receipt> const &,
        std::vector<std::vector<CallFrame>> const &,
        std::vector<Transaction> const &,
        std::vector<BlockHeader> const &ommers,
        std::optional<std::vector<Withdrawal>> const &,
        std::optional<uint64_t> round_number = std::nullopt);

    void log_debug();
};

MONAD_NAMESPACE_END
