#pragma once

#include <evmc/evmc.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_wal_action_type : uint8_t
{
    MONAD_WAL_PROPOSE = 0,
    MONAD_WAL_FINALIZE = 1,
};

static_assert(sizeof(enum monad_wal_action_type) == 1);
static_assert(alignof(enum monad_wal_action_type) == 1);

struct monad_wal_action
{
    enum monad_wal_action_type action;
    struct evmc_bytes32 id;
};

static_assert(sizeof(struct monad_wal_action) == 33);
static_assert(alignof(struct monad_wal_action) == 1);

#ifdef __cplusplus
}
#endif
