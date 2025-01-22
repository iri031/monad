#pragma once

#include <monad/config.hpp>
#include <monad/emitter/block_emitter.hpp>

#include <filesystem>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

class WalEmitter : public BlockEmitter
{
    std::ifstream cursor_;
    std::filesystem::path ledger_dir_;

public:
    WalEmitter(std::filesystem::path const &ledger_dir);

    std::optional<EmitterResult> next() override;

    bool rewind_to(monad_wal_action const &);
};

MONAD_NAMESPACE_END
