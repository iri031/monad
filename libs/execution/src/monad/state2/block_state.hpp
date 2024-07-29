#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>

#include <memory>

MONAD_NAMESPACE_BEGIN

class State;

class BlockState final
{
    Db &db_;
    StateDeltas state_{};// state changes of all the transactions in this block?
    Code code_{};// code of all the createContract transactions in this block?
// for scheduling, can we make a graph of must-happen-before constraints between the transactions and then schedule in a way that minimizes the number of transactions running concurrently that have a happens before path between them?
public:
    BlockState(Db &);

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &key);

    std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &);

    bool can_merge(State const &);

    void merge(State const &);

    void commit(std::vector<Receipt> const &);

    void log_debug();
};

MONAD_NAMESPACE_END
