#pragma once

#include <monad/statesync/statesync_messages.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_statesync_client;
struct monad_statesync_client_context;

struct monad_statesync_client_context *monad_statesync_client_context_create(
    char const *const *dbname_paths, size_t len, char const *genesis_file);

uint8_t monad_statesync_client_prefix_bytes();

size_t monad_statesync_client_prefixes();

void monad_statesync_client_handle_new_peer(
    struct monad_statesync_client_context *, uint64_t prefix, uint32_t version);

bool monad_statesync_client_handle_upsert(
    struct monad_statesync_client_context *, uint64_t prefix,
    enum monad_sync_type, unsigned char const *, uint64_t);

bool monad_statesync_client_finalize(
    struct monad_statesync_client_context *, struct monad_sync_target);

void monad_statesync_client_commit(struct monad_statesync_client_context *);

uint64_t monad_statesync_client_get_latest_block_id(
    struct monad_statesync_client_context *);

void monad_statesync_client_read_genesis(
    struct monad_statesync_client_context *);

void monad_statesync_client_context_destroy(
    struct monad_statesync_client_context *);

#ifdef __cplusplus
}
#endif
