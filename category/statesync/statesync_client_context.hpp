#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/statesync/statesync_protocol.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <filesystem>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

struct monad_statesync_client;
struct monad_sync_request;

struct monad_statesync_client_context
{
    template <class K, class V>
    using Map = ankerl::unordered_dense::segmented_map<K, V>;

    using StorageDeltas = Map<monad::bytes32_t, monad::bytes32_t>;

    using StateDelta = std::pair<monad::Account, StorageDeltas>;

    monad::OnDiskMachine machine;
    monad::mpt::Db db;
    monad::TrieDb tdb;
    std::vector<std::pair<uint64_t, uint64_t>> progress;
    std::vector<std::unique_ptr<monad::StatesyncProtocol>> protocol;
    std::array<monad::BlockHeader, 256> hdrs;
    monad::BlockHeader tgrt;
    uint64_t current;
    Map<monad::Address, StorageDeltas> buffered;
    ankerl::unordered_dense::segmented_set<monad::bytes32_t> seen_code;
    Map<monad::bytes32_t, monad::byte_string> code;
    Map<monad::Address, std::optional<StateDelta>> deltas;
    uint64_t n_upserts;
    monad_statesync_client *sync;
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request);

    monad_statesync_client_context(
        std::vector<std::filesystem::path> dbname_paths,
        std::optional<unsigned> sq_thread_cpu, monad_statesync_client *,
        void (*statesync_send_request)(
            struct monad_statesync_client *, struct monad_sync_request));

    void commit();
};
