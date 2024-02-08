#pragma once

#include <monad/config.hpp>
#include <monad/db/db.hpp>
#include <monad/lru/lru_cache.hpp>
#include <monad/state2/state_deltas.hpp>

MONAD_NAMESPACE_BEGIN

class State;

class BlockState final
{
    Db &db_;
    LruCache *lru_;
    StateDeltas state_;
    Code code_;

public:
    BlockState(Db &, LruCache * = nullptr);

    std::optional<Account> read_account(Address const &);

    bytes32_t
    read_storage(Address const &, uint64_t incarnation, bytes32_t const &key);

    byte_string read_code(bytes32_t const &code_hash);

    bool can_merge(State const &);

    void merge(State const &);

    void commit();

    void log_debug();
};

MONAD_NAMESPACE_END
