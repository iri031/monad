#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/db_cache.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>

#include <CLI/CLI.hpp>
#include <quill/Quill.h>

#include <chrono>
#include <filesystem>
#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

quill::Logger *tracer = nullptr;

MONAD_NAMESPACE_END

sig_atomic_t volatile stop;

void signal_handler(int)
{
    stop = 1;
}

using namespace monad;
namespace fs = std::filesystem;

void test_run_loop(
    fs::path const &block_db, DbRW &db, fiber::PriorityPool &priority_pool)
{
    EthereumMainnet const chain{};
    BlockHashBuffer block_hash_buffer;
    size_t block_number = 1;

    signal(SIGINT, signal_handler);
    stop = 0;

    while (stop == 0) {
        auto const path = block_db / std::to_string(block_number);
        if (!fs::exists(block_db / std::to_string(block_number + 1))) {
            continue;
        }
        MONAD_ASSERT(fs::is_regular_file(path));

        std::ifstream istream(path);
        std::ostringstream buf;
        buf << istream.rdbuf();
        auto view = byte_string_view{
            (unsigned char *)buf.view().data(), buf.view().size()};
        auto block_result = rlp::decode_block(view);
        MONAD_ASSERT(block_result.has_value());
        MONAD_ASSERT(view.empty());
        auto &block = block_result.assume_value();

        block_hash_buffer.set(block_number - 1, block.header.parent_hash);

        auto result = chain.static_validate_header(block.header);
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "block header {} {}",
                block.header.number,
                result.assume_error().message().c_str());
            break;
        }

        result = static_validate_block(EVMC_SHANGHAI, block);
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "block {} {}",
                block.header.number,
                result.assume_error().message().c_str());
            break;
        }

        auto const before = std::chrono::steady_clock::now();
        auto const receipts = execute_block(
            EVMC_SHANGHAI, block, db, block_hash_buffer, priority_pool);
        if (MONAD_UNLIKELY(receipts.has_error())) {
            LOG_ERROR(
                "block execute {} {}",
                block.header.number,
                receipts.assume_error().message().c_str());
            break;
        }

        LOG_INFO(
            "finished executing {} txns in block {}, time elasped={}",
            block.transactions.size(),
            block.header.number,
            std::chrono::steady_clock::now() - before);
        ++block_number;
    }
}

int main(int const argc, char const *argv[])
{
    using namespace monad;

    CLI::App cli{"test_run_loop"};
    cli.option_defaults()->always_capture_default();

    fs::path block_db{};
    fs::path genesis_file{};
    fs::path trace_log = std::filesystem::absolute("trace");
    std::optional<fs::path> db_path;
    unsigned nthreads = 4;
    unsigned nfibers = 32;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    auto log_level = quill::LogLevel::Info;

    cli.add_option("--block_db", block_db, "block_db directory")->required();
    cli.add_option("--trace_log", trace_log, "path to output trace file");
    cli.add_option("--genesis_file", genesis_file, "genesis file directory")
        ->required();
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "sq_thread_cpu field in io_uring_params, to specify the cpu set "
        "kernel poll thread is bound to in SQPOLL mode");
    cli.add_option("--db", db_path, "path to db");

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }
    quill::start(true);
#ifdef ENABLE_TRACING
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    tracer = quill::create_logger(
        "trace", quill::file_handler(trace_log, handler_cfg));
#endif
    quill::get_root_logger()->set_log_level(log_level);

    auto const before = std::chrono::steady_clock::now();
    auto const config = db_path.has_value()
                            ? std::make_optional(mpt::OnDiskDbConfig{
                                  .append = true, // always open existing
                                  .compaction = true,
                                  .rd_buffers = 8192,
                                  .wr_buffers = 32,
                                  .uring_entries = 128,
                                  .sq_thread_cpu = get_nprocs() - 1,
                                  .dbname_paths = {db_path.value()}})
                            : std::nullopt;
    TrieDb db{config};
    read_genesis(genesis_file, db);
    LOG_INFO(
        "finished initializing db, time elapsed = {}",
        std::chrono::steady_clock::now() - before);

    fiber::PriorityPool priority_pool{nthreads, nfibers};
    auto const start_time = std::chrono::steady_clock::now();
    DbCache db_cache{db};
    test_run_loop(block_db, db_cache, priority_pool);
    auto const elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        std::chrono::steady_clock::now() - start_time);
    LOG_INFO(
        "finished running, time_elapsed = {}",
        std::chrono::steady_clock::now() - start_time);

    return 0;
}
