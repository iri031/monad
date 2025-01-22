#pragma once

#include <monad/config.hpp>
#include <monad/db/block_db.hpp>
#include <monad/emitter/block_emitter.hpp>
#include <monad/emitter/wal_action.h>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

class ReplayEmitter : public BlockEmitter
{
    BlockDb block_db_;
    uint64_t block_num_;
    monad_wal_action_type next_state_;

public:
    ReplayEmitter(std::filesystem::path const &, uint64_t start_block = 1);

    std::optional<EmitterResult> next() override;
};

MONAD_NAMESPACE_END
