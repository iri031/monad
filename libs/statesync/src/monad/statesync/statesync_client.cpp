#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/db/trie_db.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_protocol.hpp>
#include <monad/statesync/statesync_version.h>

#include <algorithm>
#include <filesystem>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context *monad_statesync_client_context_create(
    char const *const *const dbname_paths, size_t const len,
    char const *const genesis_file)
{
    std::vector<std::filesystem::path> const paths{
        dbname_paths, dbname_paths + len};
    MONAD_ASSERT(!paths.empty());
    return new monad_statesync_client_context{paths, genesis_file};
}

uint8_t monad_statesync_client_prefix_bytes()
{
    return 1;
}

size_t monad_statesync_client_prefixes()
{
    return 1 << (8 * monad_statesync_client_prefix_bytes());
}

void monad_statesync_client_handle_new_peer(
    monad_statesync_client_context *const ctx, uint64_t const prefix,
    uint32_t const version)
{
    MONAD_ASSERT(monad_statesync_client_compatible(version));
    auto &ptr = ctx->protocol.at(prefix);
    // TODO: handle switching peers
    MONAD_ASSERT(!ptr);
    switch (version) {
    case 1:
        ptr = std::make_unique<StatesyncProtocolV1>();
        break;
    default:
        MONAD_ASSERT(false);
    };
}

bool monad_statesync_client_handle_upsert(
    monad_statesync_client_context *const ctx, uint64_t const prefix,
    monad_sync_type const type, unsigned char const *const val,
    uint64_t const size)
{
    return ctx->protocol.at(prefix)->handle_upsert(ctx, type, val, size);
}

bool monad_statesync_client_finalize(
    monad_statesync_client_context *const ctx,
    monad_sync_target const sync_target)
{
    MONAD_ASSERT(ctx->deltas.empty());
    if (!ctx->buffered.empty()) {
        // sent storage with no account
        return false;
    }
    else if (!ctx->pending.empty()) {
        // missing code
        return false;
    }

    if (sync_target.n == 0) {
        read_genesis(ctx->genesis, ctx->tdb);
    }

    if (ctx->db.get_latest_block_id() != sync_target.n) {
        ctx->db.move_trie_version_forward(
            ctx->db.get_latest_block_id(), sync_target.n);
    }
    TrieDb db{ctx->db};
    MONAD_ASSERT(db.get_block_number() == sync_target.n);

    auto const expected_root =
        to_bytes(byte_string_view{sync_target.state_root, sizeof(bytes32_t)});

    return db.state_root() == expected_root;
}

void monad_statesync_client_commit(monad_statesync_client_context *const ctx)
{
    ctx->commit();
}

uint64_t monad_statesync_client_get_latest_block_id(
    monad_statesync_client_context *const ctx)
{
    return ctx->db.get_latest_block_id();
}

void monad_statesync_client_read_genesis(
    monad_statesync_client_context *const ctx)
{
    read_genesis(ctx->genesis, ctx->tdb);
}

void monad_statesync_client_context_destroy(
    monad_statesync_client_context *const ctx)
{
    delete ctx;
}
