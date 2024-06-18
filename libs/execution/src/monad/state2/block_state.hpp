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
    StateDeltas state_{};
    Code code_{};

public:
    uint64_t total_destroyed_accounts{0};
    uint64_t total_deleted_storage{0};

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
