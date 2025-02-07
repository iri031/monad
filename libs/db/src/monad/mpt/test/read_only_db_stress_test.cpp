#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/test/test_fixtures_base.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <CLI/CLI.hpp>

#include <quill/Quill.h>

#include <atomic>
#include <chrono>
#include <filesystem>
#include <limits>
#include <list>
#include <thread>
#include <utility>

#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

#include "triedb-driver/triedb.h"

using namespace monad::mpt;
using namespace monad::test;

sig_atomic_t volatile g_done = 0;

static_assert(std::atomic<bool>::is_always_lock_free); // async signal safe

static monad::hash256 to_key(uint64_t const key)
{
    auto const as_bytes = serialize_as_big_endian<sizeof(key)>(key);
    return monad::keccak256(as_bytes);
}

static uint64_t select_rand_version(
    uint64_t earliest_block_id, uint64_t latest_block_id,
    monad::small_prng &rnd, double bias)
{
    auto const version_range_start = static_cast<double>(earliest_block_id);
    auto const version_range_end = static_cast<double>(latest_block_id);
    double r = rnd();
    r = r / monad::small_prng::max();
    if (r > 0.25) {
        r = std::pow(r, bias);
    }
    return static_cast<uint64_t>(
        version_range_start + r * (version_range_end - version_range_start));
}

static uint64_t
select_rand_version(Db const &db, monad::small_prng &rnd, double bias)
{
    return select_rand_version(
        db.get_earliest_block_id(), db.get_latest_block_id(), rnd, bias);
}

static void on_signal(int)
{
    g_done = 1;
}

int main(int argc, char *const argv[])
{
    unsigned num_sync_reader_threads = 0;
    unsigned num_async_reader_threads = 0;
    size_t num_async_reads_inflight = 100;
    unsigned num_traverse_threads = 0;
    unsigned num_triedb_driver_threads = 1;
    double prng_bias = 1.66;
    size_t num_nodes_per_version = 1;
    bool enable_compaction = true;
    bool am_unit_test = false;
    bool am_benchmark = false;
    std::optional<uint32_t> timeout_seconds;
    std::vector<std::filesystem::path> dbname_paths;
    CLI::App cli(
        "Tool for stress testing concurrent RO DB instances",
        "read_only_db_stress_test");

    try {
        cli.add_option(
            "--num-sync-reader-threads",
            num_sync_reader_threads,
            "Number of threads doing random blocking reads");
        cli.add_option(
            "--num-async-reader-threads",
            num_async_reader_threads,
            "Number of threads doing random async reads");
        cli.add_option(
            "--num-async-reads-inflight",
            num_async_reads_inflight,
            "Number of async reads to issue before calling poll");
        cli.add_option(
            "--num-traverse-threads",
            num_traverse_threads,
            "Number of threads traversing random version tries");
        cli.add_option(
            "--num-triedb-driver-threads",
            num_triedb_driver_threads,
            "Number of threads doing randomly interleaved operations with the "
            "consensus triedb-driver");
        cli.add_option(
            "--prng-bias",
            prng_bias,
            "After drawing R, raises r**bias. Can be used to choose versions "
            "earlier or later in the history");
        cli.add_option(
            "--compaction",
            enable_compaction,
            "Enable compaction when writing new DB versions");
        cli.add_option(
            "--num-nodes-per-version",
            num_nodes_per_version,
            "Number of nodes to upsert per version");
        cli.add_option(
            "--timeout",
            timeout_seconds,
            "Teardown the stress test after N seconds");
        cli.add_option(
               "--db",
               dbname_paths,
               "A comma-separated list of previously created database paths")
            ->required();
        cli.add_flag(
            "--unit-test",
            am_unit_test,
            "Run as a ten second smoke test for the test suite");
        cli.add_flag(
            "--benchmark",
            am_benchmark,
            "Run as a triedb-driver performance benchmark");
        cli.parse(argc, argv);

        quill::start(true);

        if (am_unit_test) {
            am_benchmark = true;
            dbname_paths.clear();
            dbname_paths.push_back(
                MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                "monad_read_only_stress_test_XXXXXX");
            int const fd =
                ::mkstemp((char *)dbname_paths.front().native().data());
            MONAD_ASSERT(fd != -1);
            MONAD_ASSERT(
                -1 != ::ftruncate(
                          fd, static_cast<off_t>(256ULL * 1024 * 1024 * 1024)));
            ::close(fd);
        }
        auto untempfile = monad::make_scope_exit([&]() noexcept {
            if (am_unit_test) {
                std::filesystem::remove(dbname_paths.front());
            }
        });
        if (am_benchmark) {
            timeout_seconds = am_unit_test ? 10 : 60;
            num_sync_reader_threads = 0;
            num_async_reader_threads = 0;
            num_traverse_threads = 0;
            num_triedb_driver_threads = 1;
        }

        struct sigaction sig;
        sig.sa_handler = &on_signal;
        sig.sa_flags = 0;
        sigaction(SIGINT, &sig, nullptr);

        auto const prefix = 0x00_hex;

        auto upsert_new_version = [&](Db &db, uint64_t const version) {
            UpdateList ul;

            std::list<monad::hash256> hash_alloc;
            std::list<Update> update_alloc;
            std::list<monad::byte_string> byte_alloc;
            for (size_t k = 0; k < num_nodes_per_version; ++k) {
                size_t const v = version * num_nodes_per_version + k;
                ul.push_front(update_alloc.emplace_back(make_update(
                    hash_alloc.emplace_back(to_key(v)),
                    byte_alloc.emplace_back(
                        serialize_as_big_endian<sizeof(uint64_t)>(v)))));
            }

            auto u_prefix = Update{
                .key = prefix,
                .value = monad::byte_string_view{},
                .incarnation = false,
                .next = std::move(ul)};
            UpdateList ul_prefix;
            ul_prefix.push_front(u_prefix);

            db.upsert(std::move(ul_prefix), version);
        };

        auto random_sync_read = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            Db ro_db{ro_config};

            while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID && !g_done) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
            MONAD_ASSERT(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            auto rnd = monad::thread_local_prng();
            while (!g_done) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                for (size_t k = 0; k < num_nodes_per_version; ++k) {
                    auto const v = version * num_nodes_per_version + k;
                    auto const res = ro_db.get(
                        concat(NibblesView{prefix}, NibblesView{to_key(v)}),
                        version);
                    if (res.has_value()) {
                        MONAD_ASSERT(
                            res.value() ==
                            serialize_as_big_endian<sizeof(uint64_t)>(v));
                        ++nsuccess;
                    }
                    else {
                        auto const min_version = ro_db.get_earliest_block_id();
                        MONAD_ASSERT(version < min_version);
                        ++nfailed;
                        break;
                    }
                }
            }
            std::ostringstream oss;
            oss << "Sync Reader thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed reads" << std::endl;
            std::cout << oss.str();
        };

        auto random_async_read = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            Db ro_db{ro_config};
            auto async_ctx = async_context_create(ro_db);

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID && !g_done) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
            MONAD_ASSERT(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);

            struct receiver_t
            {
                size_t *completions;
                Db *db{nullptr};
                unsigned *nsuccess{nullptr};
                unsigned *nfailed{nullptr};
                uint64_t version;
                monad::byte_string expected_value;

                void set_value(
                    monad::async::erased_connected_operation *state,
                    monad::async::result<monad::byte_string> res)
                {
                    if (res) {
                        MONAD_ASSERT(res.value() == expected_value);
                        ++(*nsuccess);
                    }
                    else {
                        auto const min_version = db->get_earliest_block_id();
                        MONAD_ASSERT(version < min_version);
                        ++(*nfailed);
                    }
                    ++(*completions);
                    delete state;
                }
            };

            size_t enqueued{};
            size_t completions{};

            auto rnd = monad::thread_local_prng();
            while (!g_done) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);

                for (size_t k = 0; k < num_nodes_per_version; ++k) {
                    auto const v = version * num_nodes_per_version + k;
                    auto *state = new auto(monad::async::connect(
                        monad::mpt::make_get_sender(
                            async_ctx.get(),
                            concat(NibblesView{prefix}, NibblesView{to_key(v)}),
                            version),
                        receiver_t{
                            &completions,
                            &ro_db,
                            &nsuccess,
                            &nfailed,
                            version,
                            serialize_as_big_endian<sizeof(uint64_t)>(v)}));
                    state->initiate();
                    ++enqueued;
                }
                if (enqueued > num_async_reads_inflight) {
                    constexpr size_t MAX_TRIEDB_ASYNC_POLLS{300'000};
                    size_t poll_count{0};
                    while (completions < enqueued &&
                           poll_count < MAX_TRIEDB_ASYNC_POLLS) {
                        ro_db.poll(true, std::numeric_limits<size_t>::max());
                        ++poll_count;
                    }
                }
            }
            std::ostringstream oss;
            oss << "Async reader thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed reads" << std::endl;
            std::cout << oss.str();
        };

        auto random_traverse = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            Db ro_db{ro_config};

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID && !g_done) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
            MONAD_ASSERT(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);

            struct VersionValidatorMachine : public TraverseMachine
            {
                Nibbles path{};
                size_t num_nodes;
                sig_atomic_t volatile &done;

                explicit VersionValidatorMachine(
                    size_t num_nodes_, sig_atomic_t volatile &done_)
                    : num_nodes(num_nodes_)
                    , done(done_)
                {
                }

                virtual bool
                down(unsigned char branch, Node const &node) override
                {
                    if (branch == INVALID_BRANCH) {
                        return true;
                    }
                    path = concat(
                        NibblesView{path}, branch, node.path_nibble_view());

                    if (node.has_value()) {
                        MONAD_ASSERT(path.nibble_size() == KECCAK256_SIZE * 2);
                        uint64_t const v =
                            deserialize_from_big_endian<uint64_t>(node.value());
                        MONAD_ASSERT(path == NibblesView{to_key(v)});
                    }
                    return !g_done;
                }

                virtual void up(unsigned char branch, Node const &node) override
                {
                    auto const path_view = NibblesView{path};
                    auto const rem_size = [&] {
                        if (branch == INVALID_BRANCH) {
                            MONAD_ASSERT(path_view.nibble_size() == 0);
                            return 0;
                        }
                        int const rem_size =
                            path_view.nibble_size() - 1 -
                            node.path_nibble_view().nibble_size();
                        MONAD_ASSERT(rem_size >= 0);
                        MONAD_ASSERT(
                            path_view.substr(static_cast<unsigned>(rem_size)) ==
                            concat(branch, node.path_nibble_view()));
                        return rem_size;
                    }();
                    path = path_view.substr(0, static_cast<unsigned>(rem_size));
                }

                virtual std::unique_ptr<TraverseMachine> clone() const override
                {
                    return std::make_unique<VersionValidatorMachine>(*this);
                }
            };

            auto rnd = monad::thread_local_prng();
            while (!g_done) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                if (auto cursor = ro_db.find(prefix, version);
                    cursor.has_value()) {
                    VersionValidatorMachine machine(
                        num_nodes_per_version, g_done);
                    machine.num_nodes = num_nodes_per_version;
                    if (!ro_db.traverse(cursor.value(), machine, version)) {
                        auto const min_version = ro_db.get_earliest_block_id();
                        MONAD_ASSERT(version < min_version);
                        ++nfailed;
                    }
                    else {
                        ++nsuccess;
                    }
                }
                else {
                    auto const min_version = ro_db.get_earliest_block_id();
                    MONAD_ASSERT(version < min_version);
                    ++nfailed;
                }
            }
            std::ostringstream oss;
            oss << "Traverse thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed traversals" << std::endl;
            std::cout << oss.str();
        };

        auto random_triedb_driver = [&] {
            struct shared_t
            {
                size_t const num_nodes_per_version;
                triedb *db = nullptr;

                unsigned nasyncread = 0;
                unsigned ntraverse_finished_normally = 0;
                unsigned ntraverse_finished_early = 0;
                unsigned nfailed = 0;

                size_t enqueued = 0;
                size_t completions = 0;
            } shared{num_nodes_per_version};

            struct traverse_state_t
            {
                shared_t &shared;
                uint64_t const version;
                size_t num_nodes_traversed{0};
            };

            MONAD_ASSERT(
                0 == triedb_open(dbname_paths.front().c_str(), &shared.db));

            while (triedb_latest_block(shared.db) == 0 && !g_done) {
            }
            // now the first version is written to db and finalized
            MONAD_ASSERT(triedb_latest_block(shared.db) != 0);

            auto async_completed = +[](bytes value, int, void *user) {
                auto *shared = (shared_t *)user;
                ++shared->nasyncread;
                ++shared->completions;
                MONAD_ASSERT(0 == triedb_finalize(value));
            };
            auto traverse_item = +[](enum triedb_async_traverse_callback kind,
                                     void *context,
                                     bytes path,
                                     size_t path_len,
                                     bytes value,
                                     size_t value_len) {
                auto *const state =
                    reinterpret_cast<traverse_state_t *>(context);
                if (kind == triedb_async_traverse_callback_finished_normally) {
                    MONAD_ASSERT_PRINTF(
                        state->num_nodes_traversed ==
                            (state->version + 1) *
                                state->shared.num_nodes_per_version,
                        "num nodes traversed %zu",
                        state->num_nodes_traversed);
                    ++state->shared.completions;
                    ++state->shared.ntraverse_finished_normally;
                    delete state;
                    return;
                }
                else if (
                    kind == triedb_async_traverse_callback_finished_early) {
                    ++state->shared.completions;
                    ++state->shared.ntraverse_finished_early;
                    delete state;
                    return;
                }
                monad::byte_string_view const path_{path, path_len};
                monad::byte_string_view const value_{value, value_len};
                MONAD_ASSERT(path_.size() == KECCAK256_SIZE);
                auto const v =
                    deserialize_from_big_endian<uint64_t>(NibblesView{value_});
                MONAD_ASSERT(NibblesView{path_} == NibblesView{to_key(v)});
                ++state->num_nodes_traversed;
            };

            auto rnd = monad::thread_local_prng();
            auto const begin = std::chrono::steady_clock::now();
            while (!g_done) {
                // auto const bits = rnd();
                auto const version = select_rand_version(
                    triedb_earliest_block(shared.db),
                    triedb_latest_block(shared.db),
                    rnd,
                    prng_bias);
                // if ((bits & 1) == 1) {
                if (false) {
                    for (size_t k = 0; k < num_nodes_per_version; ++k) {
                        auto const key = concat(
                            NibblesView{prefix},
                            NibblesView{
                                to_key(version * num_nodes_per_version + k)});
                        uint8_t keybuffer[256];
                        MONAD_ASSERT(extract_bytes_into(keybuffer, key) > 0);

                        triedb_async_read(
                            shared.db,
                            keybuffer,
                            key.nibble_size(),
                            version,
                            async_completed,
                            &shared);
                        ++shared.enqueued;
                    }
                }
                else {
                    // allocate a current state on heap, callback finish
                    // should garbage collects it
                    auto state =
                        std::make_unique<traverse_state_t>(shared, version);

                    triedb_async_traverse(
                        shared.db,
                        prefix.data(),
                        (uint8_t)prefix.size() * 2,
                        version,
                        state.release(),
                        traverse_item);
                    ++shared.enqueued;
                }
                triedb_poll(
                    shared.db, false, std::numeric_limits<size_t>::max());
            }
            while (shared.completions < shared.enqueued) {
                triedb_poll(
                    shared.db, true, std::numeric_limits<size_t>::max());
            }
            auto const end = std::chrono::steady_clock::now();
            MONAD_ASSERT(0 == triedb_close(shared.db));
            std::ostringstream oss;
            oss << "Triedb driver thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << shared.nasyncread << " async reads, "
                << shared.ntraverse_finished_normally << " finished traverses, "
                << shared.ntraverse_finished_early
                << " unfinished traverses and " << shared.nfailed
                << " failed operations" << std::endl;
            auto const totalops = shared.nasyncread +
                                  shared.ntraverse_finished_early +
                                  shared.ntraverse_finished_normally;
            oss << "   That was "
                << (1000000.0 * double(totalops) /
                    double(
                        std::chrono::duration_cast<std::chrono::microseconds>(
                            end - begin)
                            .count()))
                << " read only DB ops/sec." << std::endl;
            std::cout << oss.str();
        };

        auto open_close_read_only = [&]() {
            unsigned nsuccess = 0;
            unsigned nfailed = 0;
            while (!g_done) {
                ReadOnlyOnDiskDbConfig const ro_config{
                    .dbname_paths = dbname_paths};
                Db ro_db{ro_config};
                auto const version = ro_db.get_earliest_block_id() + 1;
                auto const v = version * num_nodes_per_version;
                auto const res = ro_db.get(
                    concat(NibblesView{prefix}, NibblesView{to_key(v)}),
                    version);
                if (res.has_value()) {
                    ++nsuccess;
                    MONAD_ASSERT(
                        res.value() ==
                        serialize_as_big_endian<sizeof(uint64_t)>(v));
                }
                else {
                    ++nfailed;
                }
            }
            std::ostringstream oss;
            oss << "Open close handle thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed queries of earliest version root" << std::endl;
            std::cout << oss.str();
        };

        // construct RWDb
        uint64_t version = 0;
        StateMachineAlwaysMerkle machine{};
        OnDiskDbConfig const config{
            .compaction = enable_compaction, .dbname_paths = {dbname_paths}};
        Db db{machine, config};

        std::cout << "Running read only DB stress test..." << std::endl;

        std::vector<std::thread> readers;
        for (unsigned i = 0; i < num_sync_reader_threads; ++i) {
            readers.emplace_back(random_sync_read);
        }

        for (unsigned i = 0; i < num_async_reader_threads; ++i) {
            readers.emplace_back(random_async_read);
        }

        for (unsigned i = 0; i < num_traverse_threads; ++i) {
            readers.emplace_back(random_traverse);
        }

        for (unsigned i = 0; i < num_triedb_driver_threads; ++i) {
            readers.emplace_back(random_triedb_driver);
        }

        readers.emplace_back(open_close_read_only);

        auto const when_to_end =
            std::chrono::steady_clock::now() +
            std::chrono::seconds(
                timeout_seconds ? *timeout_seconds
                                : /* 10 years */ (3650u * 86400u));
        while (!g_done && std::chrono::steady_clock::now() < when_to_end) {
            upsert_new_version(db, version);
            ++version;
        }
        g_done = true;
        for (auto &t : readers) {
            t.join();
        }

        std::cout << "Writer finished. Max version in RWDb is "
                  << db.get_latest_block_id() << ", min version in RWDb is "
                  << db.get_earliest_block_id() << "\n\n";
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
    }
    catch (const CLI::RequiredError &e) {
        std::cerr << "FATAL: " << e.what() << "\n\n";
        std::cerr << cli.help() << std::flush;
        return 1;
    }

    return 0;
}
