#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/db.hpp>
#include <monad/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <cstdint>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void on_commit(
    monad_statesync_server_context &ctx, StateDeltas const &state_deltas)
{
    auto const n = ctx.rw.get_block_number();
    auto const round = ctx.rw.get_round();
    MONAD_ASSERT(
        round.has_value()); // should never commit deletions to finalized nibble
    auto const round_number = round.value();

    auto &proposals = ctx.proposals;
    auto it = std::find_if(
        proposals.begin(), proposals.end(), [round_number](auto const &p) {
            return p.round == round_number;
        });

    if (it == proposals.end()) {
        proposals.emplace_back(DeletionProposal{
            .block_number = n, .round = round_number, .deletion = {}});
    }
    else {
        MONAD_ASSERT(it->block_number == n);
        if (MONAD_UNLIKELY(it->block_number != n)) {
            MONAD_ABORT(
                "Duplicate proposal for round %lu. Expected block %lu, got %lu",
                round_number,
                it->block_number,
                n);
        }
        it->deletion.clear(); // duplicate round always takes precedence
    }

    for (auto const &[addr, delta] : state_deltas) {
        auto const &account = delta.account.second;
        std::vector<bytes32_t> storage;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second &&
                    delta.second == bytes32_t{}) {
                    LOG_INFO(
                        "Deleting Storage n={} addr={} storage={} ",
                        n,
                        addr,
                        key);
                    storage.emplace_back(key);
                }
            }
        }

        if (!storage.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            if (incarnation || !account.has_value()) {
                it->deletion.emplace_back(addr, std::vector<bytes32_t>{});
            }
            if (!storage.empty()) {
                it->deletion.emplace_back(addr, std::move(storage));
            }
        }
    }
}

void on_finalize(
    monad_statesync_server_context &ctx, uint64_t const block_number,
    uint64_t const round_number)
{
    auto &proposals = ctx.proposals;

    auto winner_it = std::find_if(
        proposals.begin(), proposals.end(), [round_number](auto const &p) {
            return p.round == round_number;
        });

    if (MONAD_LIKELY(winner_it != proposals.end())) {
        constexpr auto HISTORY_LENGTH = 1200; // 20 minutes with 1s block times
        Deleted::accessor finalized_it;
        MONAD_ASSERT(ctx.deleted.emplace(
            finalized_it, block_number, std::move(winner_it->deletion)));
        if (ctx.deleted.size() > HISTORY_LENGTH) {
            MONAD_ASSERT(ctx.deleted.erase(block_number - HISTORY_LENGTH));
        }
    }

    // gc old rounds
    for (auto it = proposals.begin(); it != proposals.end();) {
        if (it->round <= round_number) {
            it = ctx.proposals.erase(it);
        }
        else {
            ++it;
        }
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

monad_statesync_server_context::monad_statesync_server_context(TrieDb &rw)
    : rw{rw}
    , ro{nullptr}
{
}

std::optional<Account>
monad_statesync_server_context::read_account(Address const &addr)
{
    return rw.read_account(addr);
}

bytes32_t monad_statesync_server_context::read_storage(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key)
{
    return rw.read_storage(addr, incarnation, key);
}

std::shared_ptr<CodeAnalysis>
monad_statesync_server_context::read_code(bytes32_t const &hash)
{
    return rw.read_code(hash);
}

bytes32_t monad_statesync_server_context::state_root()
{
    return rw.state_root();
}

bytes32_t monad_statesync_server_context::receipts_root()
{
    return rw.receipts_root();
}

bytes32_t monad_statesync_server_context::transactions_root()
{
    return rw.transactions_root();
}

std::optional<bytes32_t> monad_statesync_server_context::withdrawals_root()
{
    return rw.withdrawals_root();
}

void monad_statesync_server_context::increment_block_number()
{
    rw.increment_block_number();
}

void monad_statesync_server_context::set(
    uint64_t const block_number, uint64_t const round_number,
    uint64_t const parent_round_number)
{
    rw.set(block_number, round_number, parent_round_number);
}

void monad_statesync_server_context::finalize(
    uint64_t const block_number, uint64_t const round_number)
{
    on_finalize(*this, block_number, round_number);
    rw.finalize(block_number, round_number);
}

void monad_statesync_server_context::update_verified_block(
    uint64_t const block_number)
{
    rw.update_verified_block(block_number);
}

void monad_statesync_server_context::commit(
    StateDeltas const &state_deltas, Code const &code,
    BlockHeader const &header, std::vector<Receipt> const &receipts,
    bytes32_t const &previous_block_header_hash,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    on_commit(*this, state_deltas);
    rw.commit(
        state_deltas,
        code,
        header,
        receipts,
        previous_block_header_hash,
        call_frames,
        transactions,
        ommers,
        withdrawals);
}
