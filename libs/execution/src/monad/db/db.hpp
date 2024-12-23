#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/state2/state_deltas.hpp>

#include <cstdint>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct Db
{
    virtual std::optional<Account> read_account(Address const &) = 0;

    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) = 0;

    virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &) = 0;

    virtual bytes32_t state_root() = 0;
    virtual bytes32_t receipts_root() = 0;
    virtual bytes32_t transactions_root() = 0;
    virtual std::optional<bytes32_t> withdrawals_root() = 0;

    // for executing a proposal
    virtual void
    set(uint64_t block_number, uint64_t round_number,
        uint64_t parent_round_number) = 0;
    virtual void finalize(uint64_t block_number, uint64_t round_number) = 0;
    virtual void update_verified_block(uint64_t) = 0;

    virtual void commit(
        StateDeltas const &, Code const &, BlockHeader const &,
        std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = {std::nullopt}) = 0;

    virtual std::string print_stats()
    {
        return {};
    }
};

MONAD_NAMESPACE_END
