#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>
#include <intx/intx.hpp>

#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

class BlockState final
{
    Db &db_;
    StateDeltas state_{};
    Code code_{};
    std::vector<::intx::int256> beneficiary_balance_deltas;
    monad::Address block_beneficiary;

public:
    BlockState(Db &);

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &key);

    std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &);

    inline uint256_t sum_beneficiary_balance_deltas_upto(uint64_t tx_index) const
    {
        return std::accumulate(beneficiary_balance_deltas.begin(),
                               beneficiary_balance_deltas.begin() + tx_index,
                               uint256_t{0});
    }
    inline bool eq_beneficiary_ac_at_index(Account const &other, uint64_t tx_index) const
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_.find(it, block_beneficiary));// TODO: drop?
        assert(it->second.account.second.has_value());
        const monad::Account &beneficiary_account =
            it->second.account.second.value();
        uint256_t preblock_balance = beneficiary_account.balance;
        uint256_t beneficiary_balance =
            sum_beneficiary_balance_deltas_upto(tx_index) +
            beneficiary_account.balance;
        if (beneficiary_balance != other.balance) {
            return false;
        }
        return beneficiary_account.equal_except_balance(other);
    }

    bool can_merge(State const &, uint64_t tx_index);

    void merge(State const &, uint64_t tx_index);
    void update_beneficiary_delta(uint64_t tx_index, intx::uint256 delta);

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
