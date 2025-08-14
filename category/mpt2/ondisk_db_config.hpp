#pragma once

#include <category/mpt2/config.hpp>

#include <cstdint>
#include <filesystem>
#include <optional>

MONAD_MPT2_NAMESPACE_BEGIN

struct StateMachine;

struct OnDiskDbConfig
{
    bool append{false};
    bool compaction{false};
    bool rewind_to_latest_finalized{false};
    std::optional<uint64_t> start_block_id{std::nullopt};
    std::filesystem::path dbname_path{};
    int64_t file_size_db{512}; // truncate files to this size
    // fixed history length if contains value, otherwise rely on db to adjust
    // history length upon disk usage
    std::optional<uint64_t> fixed_history_length{std::nullopt};
};

MONAD_MPT2_NAMESPACE_END
