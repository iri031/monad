#include <monad/core/block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/update.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_protocol.hpp>

#include <deque>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context::monad_statesync_client_context(
    std::vector<std::filesystem::path> const dbname_paths,
    std::filesystem::path const genesis, monad_statesync_client *const sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request))
    : db{machine,
         mpt::OnDiskDbConfig{
             .append = true,
             .compaction = false,
             .rewind_to_latest_finalized = true,
             .rd_buffers = 8192,
             .wr_buffers = 32,
             .uring_entries = 128,
             .sq_thread_cpu = get_nprocs() - 1,
             .dbname_paths = dbname_paths}}
    , tdb{db}
    , progress(
          monad_statesync_client_prefixes(),
          {db.get_latest_block_id(), db.get_latest_block_id()})
    , protocol(monad_statesync_client_prefixes())
    , tgrt{BlockHeader{.number = mpt::INVALID_BLOCK_ID}}
    , current{db.get_latest_block_id() == mpt::INVALID_BLOCK_ID ? 0 : db.get_latest_block_id() + 1}
    , n_upserts{0}
    , genesis{genesis}
    , sync{sync}
    , statesync_send_request{statesync_send_request}
{
    auto const tdb_block_number = tdb.get_block_number();
    MONAD_ASSERT(db.get(finalized_nibbles, current).has_error());
    if (auto const latest_block = db.get_latest_block_id();
        latest_block != mpt::INVALID_BLOCK_ID) {
        MONAD_ASSERT(db.get(finalized_nibbles, latest_block).has_value());
    }
    /*
    WARNING: Direct access to mpt::Db owned by TrieDb must be handled with
    extreme caution to avoid lifetime and correctness issues.
    This is because any direct call to db.get() or db.upsert() can swap out the
    root of rwdb. However, TrieDb holds a node cursor for reading and is unaware
    when the underlying mpt::Db root becomes outdated. Continuing to look up
    from an outdated node cursor can lead to a use-after-free error.

    If TrieDb continues reading from a non-owned NodeCursor, you must reset the
    tdb block number after any db.get() operation by tdb.set_block_number() like
    below.

    A more robust solution is to avoid having TrieDb maintain a non-owned
    NodeCursor. Instead, TrieDb could record a prefix to read from directly.
    The downside, however, is that it introduces additional overhead due
    to prefix concatenation and redundant prefix lookups.
    */
    tdb.set_block_number(tdb_block_number);
    MONAD_ASSERT(db.current_block_id() == tdb_block_number);
}

void monad_statesync_client_context::commit()
{
    std::deque<mpt::Update> alloc;
    std::deque<byte_string> bytes_alloc;
    std::deque<hash256> hash_alloc;
    UpdateList accounts;
    for (auto const &[addr, delta] : deltas) {
        UpdateList storage;
        std::optional<byte_string_view> value;
        if (delta.has_value()) {
            auto const &[acct, deltas] = delta.value();
            value = bytes_alloc.emplace_back(encode_account_db(addr, acct));
            for (auto const &[key, val] : deltas) {
                storage.push_front(alloc.emplace_back(Update{
                    .key = hash_alloc.emplace_back(keccak256(key.bytes)),
                    .value = val == bytes32_t{}
                                 ? std::nullopt
                                 : std::make_optional<byte_string_view>(
                                       bytes_alloc.emplace_back(
                                           encode_storage_db(key, val))),
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(current)}));
            }
        }
        accounts.push_front(alloc.emplace_back(Update{
            .key = hash_alloc.emplace_back(keccak256(addr.bytes)),
            .value = value,
            .incarnation = false,
            .next = std::move(storage),
            .version = static_cast<int64_t>(current)}));
    }
    UpdateList code_updates;

    std::deque<bytes32_t> upserted;
    for (auto const &hash : pending) {
        if (code.contains(hash)) {
            code_updates.push_front(alloc.emplace_back(Update{
                .key = NibblesView{hash},
                .value = code.at(hash),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(current)}));
            upserted.emplace_back(hash);
        }
    }

    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(accounts),
        .version = static_cast<int64_t>(current)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(current)};
    auto const rlp = rlp::encode_block_header(tgrt);
    auto block_header_update = Update{
        .key = block_header_nibbles,
        .value = rlp,
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(block_header_update);

    UpdateList finalized_updates;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates),
        .version = static_cast<int64_t>(current)};
    finalized_updates.push_front(finalized);

    db.upsert(std::move(finalized_updates), current, false, false);

    tdb.set_block_number(current);
    for (auto const &hash : upserted) {
        MONAD_ASSERT(this->upserted.emplace(hash).second);
        MONAD_ASSERT(pending.erase(hash) == 1);
        MONAD_ASSERT(code.erase(hash) == 1);
    }
    deltas.clear();
}
