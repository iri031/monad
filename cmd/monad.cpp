#include <monad/chain/chain_config.h>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/blake3.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/likely.h>
#include <monad/core/log_level_map.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/emitter/block_emitter.hpp>
#include <monad/emitter/replay_emitter.hpp>
#include <monad/emitter/wal_action.h>
#include <monad/emitter/wal_emitter.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>
#include <monad/statesync/statesync_server_network.hpp>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>
#include <quill/handlers/FileHandler.h>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <optional>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

MONAD_NAMESPACE_END

sig_atomic_t volatile stop;

void signal_handler(int)
{
    stop = 1;
}

using namespace monad;
namespace fs = std::filesystem;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

void log_tps(
    uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
    uint64_t const gas, std::chrono::steady_clock::time_point const begin)
{
    auto const now = std::chrono::steady_clock::now();
    auto const elapsed = std::max(
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
                .count()),
        1UL); // for the unlikely case that elapsed < 1 mic
    uint64_t const tps = (ntxs) * 1'000'000 / elapsed;
    uint64_t const gps = gas / elapsed;

    LOG_INFO(
        "Run {:4d} blocks to {:8d}, number of transactions {:6d}, "
        "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
        nblocks,
        block_num,
        ntxs,
        tps,
        gps,
        monad_procfs_self_resident() / (1L << 20));
};

#pragma GCC diagnostic pop

Result<std::pair<bytes32_t, uint64_t>> on_proposal_event(
    MonadConsensusBlockHeader const &consensus_header, Block block,
    BlockHashBuffer const &block_hash_buffer, Chain const &chain, Db &db,
    fiber::PriorityPool &priority_pool, bool const is_first_block)
{
    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

    evmc_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);

    BOOST_OUTCOME_TRY(static_validate_block(rev, block));

    // Ethereum: always execute off of the parent proposal round, commit to
    // `round = block_number`, and finalize immediately after that.
    // TODO: get round number from event emitter
    db.set_block_and_round(
        block.header.number - 1,
        is_first_block ? std::nullopt
                       : std::make_optional(consensus_header.parent_round()));

    BlockState block_state(db);
    BOOST_OUTCOME_TRY(
        auto const results,
        execute_block(
            chain, rev, block, block_state, block_hash_buffer, priority_pool));

    std::vector<Receipt> receipts(results.size());
    std::vector<std::vector<CallFrame>> call_frames(results.size());
    for (unsigned i = 0; i < results.size(); ++i) {
        auto &result = results[i];
        receipts[i] = std::move(result.receipt);
        call_frames[i] = (std::move(result.call_frames));
    }

    block_state.log_debug();
    block_state.commit(
        consensus_header,
        receipts,
        call_frames,
        block.transactions,
        block.ommers,
        block.withdrawals,
        consensus_header.round);
    auto const output_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, output_header));

    return {
        to_bytes(keccak256(rlp::encode_block_header(output_header))),
        output_header.gas_used};
}

Result<std::pair<uint64_t, uint64_t>> run_monad(
    Chain const &chain, Db &db, BlockHashChain &block_hash_chain,
    BlockEmitter &emitter, fiber::PriorityPool &priority_pool,
    uint64_t &block_num, uint64_t const nblocks)
{
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);
    signal(SIGINT, signal_handler);
    stop = 0;

    uint64_t const batch_size =
        nblocks == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;

    uint64_t const end_block_num =
        (std::numeric_limits<uint64_t>::max() - block_num + 1) <= nblocks
            ? std::numeric_limits<uint64_t>::max()
            : block_num + nblocks - 1;
    uint64_t const init_block_num = block_num;
    while (block_num <= end_block_num && stop == 0) {
        auto const emitter_res = emitter.next();
        if (!emitter_res.has_value()) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }

        auto const &[action, block, consensus_header] = emitter_res.value();
        switch (action) {
        case MONAD_WAL_PROPOSE: {
            auto const &block_hash_buffer =
                block_hash_chain.find_chain(consensus_header.parent_round());
            BOOST_OUTCOME_TRY(
                auto const proposal_output,
                on_proposal_event(
                    consensus_header,
                    block,
                    block_hash_buffer,
                    chain,
                    db,
                    priority_pool,
                    block.header.number == init_block_num));
            block_hash_chain.propose(
                proposal_output.first,
                consensus_header.round,
                consensus_header.parent_round());

            auto const &verified_blocks =
                consensus_header.delayed_execution_results;
            if (MONAD_LIKELY(!verified_blocks.empty())) {
                db.update_verified_block(verified_blocks.back().number);
            }
            ntxs += block.transactions.size();
            batch_num_txs += block.transactions.size();
            total_gas += proposal_output.second;
            batch_gas += proposal_output.second;
        } break;
        case MONAD_WAL_FINALIZE: {
            db.finalize(
                consensus_header.execution_inputs.number,
                consensus_header.round);
            block_hash_chain.finalize(consensus_header.round);

            ++batch_num_blocks;

            if (block_num % batch_size == 0) {
                log_tps(
                    block_num,
                    batch_num_blocks,
                    batch_num_txs,
                    batch_gas,
                    batch_begin);
                batch_num_blocks = 0;
                batch_num_txs = 0;
                batch_gas = 0;
                batch_begin = std::chrono::steady_clock::now();
            }
            ++block_num;
        } break;
        }
    }
    if (batch_num_blocks > 0) {
        log_tps(
            block_num, batch_num_blocks, batch_num_txs, batch_gas, batch_begin);
    }
    return {ntxs, total_gas};
}

int main(int const argc, char const *argv[])
{

    CLI::App cli{"monad"};
    cli.option_defaults()->always_capture_default();

    monad_chain_config chain_config;
    fs::path block_db_path;
    uint64_t nblocks = std::numeric_limits<uint64_t>::max();
    unsigned nthreads = 4;
    unsigned nfibers = 256;
    bool no_compaction = false;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    unsigned ro_sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 2);
    std::vector<fs::path> dbname_paths;
    fs::path genesis;
    fs::path snapshot;
    fs::path dump_snapshot;
    std::string statesync;
    auto log_level = quill::LogLevel::Info;

    std::unordered_map<std::string, monad_chain_config> const CHAIN_CONFIG_MAP =
        {{"ethereum_mainnet", CHAIN_CONFIG_ETHEREUM_MAINNET},
         {"monad_devnet", CHAIN_CONFIG_MONAD_DEVNET},
         {"monad_testnet", CHAIN_CONFIG_MONAD_TESTNET}};

    cli.add_option("--chain", chain_config, "select which chain config to run")
        ->transform(CLI::CheckedTransformer(CHAIN_CONFIG_MAP, CLI::ignore_case))
        ->required();
    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("--nblocks", nblocks, "number of blocks to execute");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_flag("--no-compaction", no_compaction, "disable compaction");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "sq_thread_cpu field in io_uring_params, to specify the cpu set "
        "kernel poll thread is bound to in SQPOLL mode");
    cli.add_option(
        "--ro_sq_thread_cpu",
        ro_sq_thread_cpu,
        "sq_thread_cpu for the read only db");
    cli.add_option(
        "--db",
        dbname_paths,
        "A comma-separated list of previously created database paths. You can "
        "configure the storage pool with one or more files/devices. If no "
        "value is passed, the replay will run with an in-memory triedb");
    cli.add_option(
        "--dump_snapshot",
        dump_snapshot,
        "directory to dump state to at the end of run");
    auto *const group =
        cli.add_option_group("load", "methods to initialize the db");
    group->add_option("--genesis", genesis, "genesis file")
        ->check(CLI::ExistingFile);
    group
        ->add_option(
            "--snapshot", snapshot, "snapshot file path to load db from")
        ->check([](std::string const &s) -> std::string {
            fs::path const path{s};
            if (!fs::is_regular_file(path / "accounts")) {
                return "missing accounts";
            }
            if (!fs::is_regular_file(path / "code")) {
                return "missing code";
            }
            return "";
        });
    group->add_option(
        "--statesync", statesync, "socket for statesync communication");
    group->require_option(1);
#ifdef ENABLE_EVENT_TRACING
    fs::path trace_log = fs::absolute("trace");
    cli.add_option("--trace_log", trace_log, "path to output trace file");
#endif

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }

    auto stdout_handler = quill::stdout_handler();
    stdout_handler->set_pattern(
        "%(ascii_time) [%(thread)] %(filename):%(lineno) LOG_%(level_name)\t"
        "%(message)",
        "%Y-%m-%d %H:%M:%S.%Qns",
        quill::Timezone::GmtTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(stdout_handler);
    quill::configure(cfg);
    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
    LOG_INFO("running with commit '{}'", GIT_COMMIT_HASH);

#ifdef ENABLE_EVENT_TRACING
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    event_tracer = quill::create_logger(
        "event_trace", quill::file_handler(trace_log, handler_cfg));
#endif

    auto const db_in_memory = dbname_paths.empty();
    [[maybe_unused]] auto const load_start_time =
        std::chrono::steady_clock::now();

    std::optional<monad_statesync_server_network> net;
    if (!statesync.empty()) {
        net.emplace(statesync.c_str());
    }
    std::unique_ptr<mpt::StateMachine> machine;
    mpt::Db db = [&] {
        if (!db_in_memory) {
            machine = std::make_unique<OnDiskMachine>();
            return mpt::Db{
                *machine,
                mpt::OnDiskDbConfig{
                    .append = true,
                    .compaction = !no_compaction,
                    .rd_buffers = 8192,
                    .wr_buffers = 32,
                    .uring_entries = 128,
                    .sq_thread_cpu = sq_thread_cpu,
                    .dbname_paths = dbname_paths}};
        }
        machine = std::make_unique<InMemoryMachine>();
        return mpt::Db{*machine};
    }();

    TrieDb triedb{db}; // init block number to latest finalized block
    // Note: in memory db block number is always zero
    uint64_t const init_block_num = [&] {
        if (!snapshot.empty()) {
            if (db.root().is_valid()) {
                throw std::runtime_error(
                    "can not load checkpoint into non-empty database");
            }
            LOG_INFO("Loading from binary checkpoint in {}", snapshot);
            std::ifstream accounts(snapshot / "accounts");
            std::ifstream code(snapshot / "code");
            auto const n = std::stoul(snapshot.stem());
            load_from_binary(db, accounts, code, n);

            // load the eth header for snapshot
            BlockDb block_db{block_db_path};
            Block block;
            MONAD_ASSERT_PRINTF(
                block_db.get(n, block), "FATAL: Could not load block %lu", n);
            load_header(db, block.header);
            return n;
        }
        else if (!db.root().is_valid()) {
            MONAD_ASSERT(statesync.empty());
            LOG_INFO("loading from genesis {}", genesis);
            TrieDb tdb{db};
            read_genesis(genesis, tdb);
        }
        return triedb.get_block_number();
    }();

    std::optional<monad_statesync_server_context> ctx;
    std::jthread sync_thread;
    monad_statesync_server *sync = nullptr;
    if (!statesync.empty()) {
        ctx.emplace(triedb);
        sync = monad_statesync_server_create(
            &ctx.value(),
            &net.value(),
            &statesync_server_recv,
            &statesync_server_send_upsert,
            &statesync_server_send_done);
        sync_thread = std::jthread([&](std::stop_token const token) {
            pthread_setname_np(pthread_self(), "statesync thread");
            mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{
                .sq_thread_cpu = ro_sq_thread_cpu,
                .dbname_paths = dbname_paths}};
            ctx->ro = &ro;
            while (!token.stop_requested()) {
                monad_statesync_server_run_once(sync);
            }
            ctx->ro = nullptr;
        });
    }

    LOG_INFO(
        "Finished initializing db at block = {}, last finalized block = {}, "
        "last verified block = {}, state root = {}, time elapsed "
        "= {}",
        init_block_num,
        db.get_latest_finalized_block_id(),
        db.get_latest_verified_block_id(),
        triedb.state_root(),
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - load_start_time));

    uint64_t const start_block_num = init_block_num + 1;

    LOG_INFO(
        "Running with block_db = {}, start block number = {}, "
        "number blocks = {}",
        block_db_path,
        start_block_num,
        nblocks);

    fiber::PriorityPool priority_pool{nthreads, nfibers};

    auto const start_time = std::chrono::steady_clock::now();

    auto chain = [chain_config] -> std::unique_ptr<Chain> {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return std::make_unique<EthereumMainnet>();
        case CHAIN_CONFIG_MONAD_DEVNET:
            return std::make_unique<MonadDevnet>();
        case CHAIN_CONFIG_MONAD_TESTNET:
            return std::make_unique<MonadTestnet>();
        }
        MONAD_ASSERT(false);
    }();

    auto const emitter = [&] -> std::unique_ptr<BlockEmitter> {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return std::make_unique<ReplayEmitter>(
                block_db_path, start_block_num);
        case CHAIN_CONFIG_MONAD_DEVNET:
        case CHAIN_CONFIG_MONAD_TESTNET: {
            auto emitter = std::make_unique<WalEmitter>(block_db_path);
            auto encoded_bft_header = db.get(
                mpt::concat(FINALIZED_NIBBLE, BFT_BLOCK_NIBBLE),
                init_block_num);
            if (encoded_bft_header.has_value()) {
                auto const bft_block_id =
                    to_bytes(blake3(encoded_bft_header.value()));
                monad_wal_action const rewind_action{
                    .action = MONAD_WAL_PROPOSE, .id = bft_block_id};
                if (emitter->rewind_to(rewind_action)) {
                    emitter->next(); // skip this proposal
                }
            }
            return emitter;
        }
        }
        MONAD_ASSERT(false);
    }();

    BlockHashBufferFinalized block_hash_buffer;
    bool initialized_headers_from_triedb = false;

    if (!db_in_memory) {
        mpt::Db rodb{mpt::ReadOnlyOnDiskDbConfig{
            .sq_thread_cpu = ro_sq_thread_cpu, .dbname_paths = dbname_paths}};
        initialized_headers_from_triedb = init_block_hash_buffer_from_triedb(
            rodb, start_block_num, block_hash_buffer);
    }
    if (!initialized_headers_from_triedb) {
        BlockDb block_db{block_db_path};
        MONAD_ASSERT(chain_config == CHAIN_CONFIG_ETHEREUM_MAINNET);
        MONAD_ASSERT(init_block_hash_buffer_from_blockdb(
            block_db, start_block_num, block_hash_buffer));
    }

    BlockHashChain block_hash_chain(block_hash_buffer);
    uint64_t block_num = start_block_num;
    auto const result = run_monad(
        *chain,
        ctx ? static_cast<Db &>(*ctx) : static_cast<Db &>(triedb),
        block_hash_chain,
        *emitter,
        priority_pool,
        block_num,
        nblocks);

    if (MONAD_UNLIKELY(result.has_error())) {
        LOG_ERROR(
            "block {} failed with: {}",
            block_num,
            result.assume_error().message().c_str());
    }
    else {
        [[maybe_unused]] auto const elapsed =
            std::chrono::duration_cast<std::chrono::seconds>(
                std::chrono::steady_clock::now() - start_time);
        LOG_INFO(
            "Finish running, finish(stopped) block number = {}, "
            "number of blocks run = {}, time_elapsed = {}, num transactions = "
            "{}, "
            "tps = {}, gps = {} M",
            block_num,
            nblocks,
            elapsed,
            result.assume_value().first,
            result.assume_value().first /
                std::max(1UL, static_cast<uint64_t>(elapsed.count())),
            result.assume_value().second /
                (1'000'000 *
                 std::max(1UL, static_cast<uint64_t>(elapsed.count()))));
    }

    if (sync != nullptr) {
        sync_thread.request_stop();
        sync_thread.join();
        monad_statesync_server_destroy(sync);
    }

    if (!dump_snapshot.empty()) {
        LOG_INFO("Dump db of block: {}", block_num);
        mpt::Db db{mpt::ReadOnlyOnDiskDbConfig{
            .sq_thread_cpu = ro_sq_thread_cpu,
            .dbname_paths = dbname_paths,
            .concurrent_read_io_limit = 128}};
        TrieDb ro_db{db};
        write_to_file(ro_db.to_json(), dump_snapshot, block_num);
    }
    return result.has_error() ? EXIT_FAILURE : EXIT_SUCCESS;
}
