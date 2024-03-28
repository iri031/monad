#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db_cache.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/execution/trace.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>

#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

using eth_start_fork = fork_traits::shanghai;

quill::Logger *tracer = nullptr;

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"replay_ethereum"};
    cli.option_defaults()->always_capture_default();

    std::filesystem::path block_db_path{};
    std::filesystem::path genesis_file_path{};
    std::optional<block_num_t> finish_block_number = std::nullopt;
    std::optional<uint64_t> block_id_continue = std::nullopt;
    bool no_compaction = false;
    unsigned nthreads = 4;
    unsigned nfibers = 256;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    std::vector<std::filesystem::path> dbname_paths;
    std::filesystem::path load_snapshot{};
    std::filesystem::path dump_snapshot{};
    std::filesystem::path trace_log = std::filesystem::absolute("trace");

    quill::start(true);

    /* Note on triedb block number prefix: in memory triedb remains a single
    version db, with block number prefix always 0. On disk triedb maintains the
    state history where each block state starts after the corresponding block
    number prefix.
    */
    auto log_level = quill::LogLevel::Info;

    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("--trace_log", trace_log, "path to output trace file");
    auto *has_genesis_file = cli.add_option(
        "--genesis_file", genesis_file_path, "genesis file directory");
    cli.add_option(
        "--finish", finish_block_number, "1 pass the last executed block");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads. Default is 4.");
    cli.add_option("--nfibers", nfibers, "number of fibers. Default is 256.");
    cli.add_flag(
        "--no-compaction",
        no_compaction,
        "do not do compaction. Default is do compaction.");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "sq_thread_cpu field in io_uring_params, to specify the cpu set kernel "
        "poll thread is bound to in SQPOLL mode. Default is the last CPU in "
        "the system.");
    auto const on_disk_option = cli.add_option(
        "--db",
        dbname_paths,
        "A comma-separated list of previously created database paths. You can "
        "configure the storage pool with one or more files/devices. If no "
        "value is passed, the replay will run with an in-memory triedb");
    auto const snapshot_option = cli.add_option(
        "--load_snapshot", load_snapshot, "snapshot file path to load db from");
    auto const resume_option = cli.add_option(
        "--block_id_continue",
        block_id_continue,
        "block id to continue running from an existing on disk TrieDb "
        "instance");
    cli.add_option(
        "--dump_snapshot",
        dump_snapshot,
        "directory to dump state to at the end of run");

    snapshot_option->excludes(resume_option);
    resume_option->needs(on_disk_option);

    try {
        cli.parse(argc, argv);
    }
    catch (const CLI::CallForHelp &e) {
        return cli.exit(e);
    }

#ifdef ENABLE_TRACING
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    tracer = quill::create_logger(
        "trace", quill::file_handler(trace_log, handler_cfg));
#endif

    auto block_db = BlockDb(block_db_path);

    auto const load_start_time = std::chrono::steady_clock::now();

    bool const on_disk = !dbname_paths.empty();

    auto const config = on_disk ? std::make_optional(mpt::OnDiskDbConfig{
                                      .append = true, // always open existing
                                      .compaction = !no_compaction,
                                      .rd_buffers = 8192,
                                      .wr_buffers = 32,
                                      .uring_entries = 128,
                                      .sq_thread_cpu = sq_thread_cpu,
                                      .start_block_id = block_id_continue,
                                      .dbname_paths = dbname_paths})
                                : std::nullopt;
    uint64_t init_block_number = 0;
    auto db = [&] -> db::TrieDb {
        if (load_snapshot.empty()) {
            return db::TrieDb{config};
        }
        MONAD_ASSERT(!block_id_continue.has_value());
        namespace fs = std::filesystem;
        if (!(fs::is_directory(load_snapshot) &&
              (fs::exists(load_snapshot / "state.json") ||
               (fs::exists(load_snapshot / "accounts") &&
                fs::exists(load_snapshot / "code"))))) {
            throw std::runtime_error(
                "Invalid snapshot folder provided. Please ensure that the "
                "directory you pass contains the block number of the snapshot "
                "in its path and includes either files 'accounts' and 'code', "
                "or 'state.json'.");
        }
        init_block_number = std::stoul(load_snapshot.stem());
        if (fs::exists(load_snapshot / "accounts")) {
            MONAD_ASSERT(fs::exists(load_snapshot / "code"));
            LOG_INFO("Loading from binary checkpoint in {}", load_snapshot);
            std::ifstream accounts(load_snapshot / "accounts");
            std::ifstream code(load_snapshot / "code");
            return db::TrieDb{config, accounts, code, init_block_number};
        }
        MONAD_ASSERT(fs::exists(load_snapshot / "state.json"));
        LOG_INFO("Loading from json checkpoint in {}", load_snapshot);
        std::ifstream ifile_stream(load_snapshot / "state.json");
        return db::TrieDb{config, ifile_stream, init_block_number};
    }();

    if (load_snapshot.empty()) {
        init_block_number = db.current_block_number();
    }
    if (init_block_number == 0) {
        MONAD_ASSERT(*has_genesis_file);
        read_and_verify_genesis(block_db, db, genesis_file_path);
    }

    auto const load_finish_time = std::chrono::steady_clock::now();
    auto const load_elapsed =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            load_finish_time - load_start_time);
    LOG_INFO(
        "Finished initializing db at block = {}, time elapsed = {}",
        init_block_number,
        load_elapsed);

    quill::get_root_logger()->set_log_level(log_level);

    uint64_t const start_block_number = init_block_number + 1;

    if (finish_block_number.has_value() &&
        finish_block_number.value() <= start_block_number) {
        throw std::runtime_error(fmt::format(
            "Finish block number must be larger than start block "
            "number {}, please try a larger finish block number",
            start_block_number));
    }

    LOG_INFO(
        "Running with block_db = {}, start_block_number = {}, "
        "finish block number = {}",
        block_db_path,
        start_block_number,
        finish_block_number);

    fiber::PriorityPool priority_pool{nthreads, nfibers};

    ReplayFromBlockDb replay_eth;

    auto const start_time = std::chrono::steady_clock::now();

    DbCache db_cache{db};

    auto result = replay_eth.run<eth_start_fork>(
        db_cache,
        block_db,
        priority_pool,
        start_block_number,
        finish_block_number);

    auto const finish_time = std::chrono::steady_clock::now();
    auto const elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        finish_time - start_time);

    LOG_INFO(
        "Finish running, status = {}, finish(stopped) block number = {}, "
        "number of blocks run = {}, time_elapsed = {}, num transactions = {}, "
        "tps = {}",
        static_cast<int>(result.status),
        result.block_number,
        result.block_number - start_block_number + 1,
        elapsed,
        replay_eth.n_transactions,
        replay_eth.n_transactions /
            std::max(1UL, static_cast<uint64_t>(elapsed.count())));

    if (!dump_snapshot.empty()) {
        LOG_INFO("Dump db of block: {}", result.block_number);
        db::write_to_file(db.to_json(), dump_snapshot, result.block_number);
    }
    return 0;
}
