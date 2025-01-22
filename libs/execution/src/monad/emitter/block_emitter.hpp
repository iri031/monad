#pragma once

#include <monad/config.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/emitter/wal_action.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct BlockEmitter
{
    struct EmitterResult
    {
        monad_wal_action_type action;
        Block block;
        MonadConsensusBlockHeader header;
    };

    virtual std::optional<EmitterResult> next() = 0;
    virtual ~BlockEmitter() = default;
};

MONAD_NAMESPACE_END
