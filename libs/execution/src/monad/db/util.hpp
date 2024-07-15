#pragma once

#include <monad/config.hpp>
#include <monad/db/trie_db.hpp>

#include <nlohmann/json.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

void incremental_write_to_file(
    TrieDb &, std::filesystem::path const &, uint64_t const);

MONAD_NAMESPACE_END
