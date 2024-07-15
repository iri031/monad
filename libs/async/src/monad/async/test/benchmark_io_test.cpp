#include <CLI/CLI.hpp>

#include <monad/async/config.hpp>
#include <monad/async/cpp_helpers.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/executor.h>
#include <monad/async/io.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/async/task.h>
#include <monad/async/util.h>
#include <monad/core/assert.h>
#include <monad/core/small_prng.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mem/huge_mem.hpp>

#include <algorithm>
#include <cerrno>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <filesystem>
#include <iostream>
#include <span>
#include <sstream>
#include <stdexcept>
#include <system_error>
#include <tuple>
#include <utility>
#include <vector>

#if MONAD_HAVE_LIBCAP
    #include <linux/capability.h>
    #include <sys/capability.h>
#endif
#include <unistd.h>

// These test a raw block device with 75% of chunks full

/* This is the codebase from start of July 2024

./benchmark_io_test_main1 --storage /dev/mapper/raid0-rawblk1 --workload 0

Total ops/sec: 243310 mean latency: 314526 min: 72311 max: 1.05242e+06


./benchmark_io_test_main1 --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15

Total ops/sec: 312201 mean latency: 576083 min: 75852 max: 2.19743e+06


./benchmark_io_test_main1 --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15 --concurrent-io 64

Total ops/sec: 290986 mean latency: 219821 min: 62501 max: 757597




This is the codebase from right now (mid August 2024) - note that the
benchmark test has changed since to fix bugs which were incorrecyly boosting
results

./benchmark_io_test_main2 --storage /dev/mapper/raid0-rawblk1 --workload 0

Total ops/sec: 241384 mean latency: 318730 min: 54522 max: 1.7509e+06


./benchmark_io_test_main2 --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15

Total ops/sec: 312703 mean latency: 581221 min: 89132 max: 2.13405e+06


./benchmark_io_test_main2 --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15 --concurrent-io 64

Total ops/sec: 291103 mean latency: 219732 min: 65601 max: 740587




This is the AsyncIO wrapper of the new i/o executor at mid August 2024.

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0

Total ops/sec: 185334 mean latency: 1.10067e+07 min: 1.02387e+07
max: 2.33998e+07

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15

Total ops/sec: 322897 mean latency: 6.32644e+06 min: 5.5215e+06 max: 1.65021e+07


./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15 --concurrent-io 64

Total ops/sec: 254484 mean latency: 235690 min: 69342 max: 1.1954e+06




This is the new i/o executor direct at mid August 2024.

./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--new-io-executor

Total ops/sec: 303884 mean latency: 557550 min: 306297 max: 1.3066e+07


./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15 --new-io-executor

Total ops/sec: 319918 mean latency: 562282 min: 309937 max: 1.00402e+07


./benchmark_io_test_wrapped --storage /dev/mapper/raid0-rawblk1 --workload 0
--kernel-poll-thread 15 --concurrent-io 64 --new-io-executor

Total ops/sec: 298526 mean latency: 211974 min: 66621 max: 8.1498e+06




AsyncIO wrapper is 23% slower for the syscall io_uring, but 3.3% faster for the
sqpoll io_uring (but 12.6% slower for the 64 concurrent i/o case).

Native is 26% faster for the syscall io_uring and 2.3% faster for the sqpoll
io_uring (I think that is measurement noise, it should be faster than the
AsyncIO wrapper)
*/

struct shared_state_t
{
    std::vector<std::pair<uint32_t, uint32_t>> const
        chunk_sizes_div_disk_page_size;

    bool done{false};
    uint32_t ops{0};
    uint64_t min_ns, max_ns, acc_ns;
    monad::small_prng rand;

    constexpr explicit shared_state_t(MONAD_ASYNC_NAMESPACE::AsyncIO &io)
        : chunk_sizes_div_disk_page_size([&] {
            std::vector<std::pair<uint32_t, uint32_t>> ret(io.chunk_count());
            for (uint32_t n = 0; n < uint32_t(ret.size()); n++) {
                ret[n] = {
                    n,
                    uint32_t(
                        io.storage_pool()
                            .chunk(MONAD_ASYNC_NAMESPACE::storage_pool::seq, n)
                            ->size() /
                        MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE)};
                if (ret[n].second > 0) {
                    // Prevent random reads off the end of the chunk
                    ret[n].second--;
                }
            }
            ret.erase(
                std::remove_if(
                    ret.begin(),
                    ret.end(),
                    [](auto const &x) { return x.second == 0; }),
                ret.end());
            return ret;
        }())
    {
    }

    MONAD_ASYNC_NAMESPACE::file_offset_t test_surface_available() const noexcept
    {
        MONAD_ASYNC_NAMESPACE::file_offset_t ret = 0;
        for (auto const &i : chunk_sizes_div_disk_page_size) {
            ret += i.second;
        }
        ret *= MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE;
        return ret;
    }

    MONAD_ASYNC_NAMESPACE::chunk_offset_t add_op(uint64_t elapsed_ns)
    {
        ops++;
        if (elapsed_ns < min_ns) {
            min_ns = elapsed_ns;
        }
        if (elapsed_ns > max_ns) {
            max_ns = elapsed_ns;
        }
        acc_ns += elapsed_ns;
        auto r = rand();
        auto [chunk_id, chunk_size_div_disk_page_size] =
            chunk_sizes_div_disk_page_size
                [r % uint32_t(chunk_sizes_div_disk_page_size.size())];
        auto offset_into_chunk = (r >> 16) % chunk_size_div_disk_page_size;
        return MONAD_ASYNC_NAMESPACE::chunk_offset_t(
            chunk_id,
            offset_into_chunk * MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE);
    }
};

struct receiver_t
{
    static constexpr bool lifetime_managed_internally = false;

    shared_state_t *shared;

    explicit receiver_t(shared_state_t *shared_)
        : shared(shared_)
    {
    }

    inline void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *rawstate,
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type buffer);

    void reset() {}
};

using connected_state_ptr_type =
    MONAD_ASYNC_NAMESPACE::AsyncIO::connected_operation_unique_ptr_type<
        MONAD_ASYNC_NAMESPACE::read_single_buffer_sender, receiver_t>;

inline void receiver_t::set_value(
    MONAD_ASYNC_NAMESPACE::erased_connected_operation *rawstate,
    MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::result_type buffer)
{
    if (!buffer) {
        std::cerr << "FATAL: " << buffer.assume_error().message().c_str()
                  << std::endl;
    }
    MONAD_ASSERT(buffer);
    auto const elapsed_ns(uint64_t(
        std::chrono::duration_cast<std::chrono::nanoseconds>(rawstate->elapsed)
            .count()));
    auto const offset = shared->add_op(elapsed_ns);
    if (!shared->done) {
        auto *state =
            static_cast<connected_state_ptr_type::element_type *>(rawstate);
        auto const io_priority = state->io_priority();
        state->reset(
            std::tuple{offset, MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE},
            std::tuple{});
        state->set_io_priority(io_priority);
        state->initiate();
    }
}

int main(int argc, char *argv[])
{
    CLI::App cli("Tool for benchmarking the i/o engine", "benchmark_io_test");
    cli.footer(R"(Suitable sources of block storage:

1. Raw partitions on a storage device.
2. The storage device itself.
3. A file on a filing system (use 'truncate -s 1T sparsefile' to create and
set it to the desired size beforehand).
)");
    try {
        bool destroy_and_fill = false;
        unsigned destroy_and_really_fill_count = 0;
        std::vector<std::filesystem::path> storage_paths;
        monad::io::RingConfig ringconfig{128};
        unsigned concurrent_io = 2048;
        unsigned concurrent_read_io_limit = 0;
        bool eager_completions = false;
        bool highest_io_priority = false;
        bool new_io_executor = false;
        unsigned workload_us = 5;
        unsigned duration_secs = 30;
        cli.add_option(
               "--storage",
               storage_paths,
               "one or more sources of block storage (must be at least 256Mb + "
               "4Kb long).")
            ->required();
        cli.add_flag(
            "--fill",
            destroy_and_fill,
            "destroy all existing contents, mark all chunks as full before "
            "doing test.");
        cli.add_option(
            "--really-fill",
            destroy_and_really_fill_count,
            "destroy all existing contents, actually fill chunks specified "
            "before "
            "doing test.");
        cli.add_option(
            "--concurrent-io",
            concurrent_io,
            "how many i/o this test program should do concurrently. Default is "
            "2048.");

        cli.add_option(
            "--ring-entries",
            ringconfig.entries,
            "how many submission entries io_uring should have. Default is "
            "128.");
        cli.add_flag(
            "--enable-io-polling",
            ringconfig.enable_io_polling,
            "whether to enable i/o polling within the kernel. Default is no "
            "i/o polling.");
        cli.add_option(
            "--kernel-poll-thread",
            ringconfig.sq_thread_cpu,
            "on what CPU to run a spin polling thread within the kernel. "
            "Default is no kernel thread.");
        cli.add_option(
            "--concurrent-read-io-limit",
            concurrent_read_io_limit,
            "maximum number of read i/o to issue at a time. This differs from "
            "--concurrent-io because it tells AsyncIO to ensure concurrent i/o "
            "does not exceed this, whereas --concurrent-io tells this test "
            "program how many i/o to do. Default is no "
            "limit.");
        cli.add_flag(
            "--eager-completions",
            eager_completions,
            "whether to reap completions as eagerly as possible. Default is "
            "reaping as needed.");
        cli.add_flag(
            "--highest-io-priority",
            highest_io_priority,
            "whether to set highest i/o priority possible, which is sent on to "
            "the storage device and may encourage it to minimise latency. "
            "Default is not set.");
        cli.add_option(
            "--workload",
            workload_us,
            "how long the simulated workload should last each time in "
            "microseconds. Default is five microseconds.");
        cli.add_option(
            "--duration",
            duration_secs,
            "how long the benchmark should run for in seconds. Default is "
            "thirty seconds.");
        cli.add_flag(
            "--new-io-executor",
            new_io_executor,
            "whether to use the new i/o executor directly instead of via its "
            "AsyncIO wrapper. Default is no.");
        cli.parse(argc, argv);

#if MONAD_HAVE_LIBCAP
        if (highest_io_priority) {
            // We will need the CAP_SYS_NICE capability for this to work
            MONAD_ASSERT(CAP_IS_SUPPORTED(CAP_SYS_NICE));
            auto *caps = cap_get_proc();
            MONAD_ASSERT(caps != nullptr);
            auto uncaps =
                monad::make_scope_exit([&]() noexcept { cap_free(caps); });
            cap_value_t const cap_list[] = {CAP_SYS_NICE};
            if (cap_set_flag(caps, CAP_EFFECTIVE, 1, cap_list, CAP_SET) == -1 ||
                cap_set_proc(caps) == -1) {
                std::cerr
                    << "FATAL: To use --highest-io-priority the process needs "
                       "the CAP_SYS_NICE capability. To assign that, "
                       "do:\n\nsudo setcap cap_sys_nice+ep "
                       "benchmark_io_test\n\nAnd run it again."
                    << std::endl;
                return 1;
            }
        }
#else // MONAD_HAVE_LIBCAP
        MONAD_ASSERT(!highest_io_priority); // Not supported without libcap
#endif
        if (destroy_and_really_fill_count > 0) {
            destroy_and_fill = true;
        }

        auto const mode =
            destroy_and_fill
                ? MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate
                : MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing;
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags{};
        flags.interleave_chunks_evenly = true;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{{storage_paths}, mode, flags};

        monad::io::Ring ring(ringconfig);
        monad::io::Buffers rwbuf = monad::io::make_buffers_for_read_only(
            ring,
            concurrent_io,
            MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE);
        auto io = MONAD_ASYNC_NAMESPACE::AsyncIO{pool, rwbuf};
        if (destroy_and_really_fill_count > 0) {
            uint32_t const tofill = std::min(
                uint32_t(destroy_and_really_fill_count),
                uint32_t(io.chunk_count()));
            monad::small_prng rand;
            std::span<uint32_t> buffer;
            monad::HugeMem storage;
            auto make_storage = [&](size_t bytes) {
                storage = monad::HugeMem{bytes};
                buffer = {
                    (uint32_t *)storage.get_data(),
                    storage.get_size() / sizeof(uint32_t)};
                for (auto &p : buffer) {
                    p = rand();
                }
            };
            for (uint32_t n = 0; n < tofill; n++) {
                auto const bytes = uint32_t(io.chunk_capacity(n));
                auto [fd, offset] = pool.chunk(pool.seq, n)->write_fd(bytes);
                if (buffer.size_bytes() < bytes) {
                    make_storage(bytes);
                }
                auto const written =
                    ::pwrite(fd, buffer.data(), bytes, off_t(offset));
                if (written < 0) {
                    throw std::system_error(errno, std::system_category());
                }
                MONAD_ASSERT(written > 0);
            }
        }
        else if (destroy_and_fill) {
            for (uint32_t n = 0; n < io.chunk_count(); n++) {
                pool.chunk(pool.seq, n)
                    ->write_fd(uint32_t(io.chunk_capacity(n)));
            }
        }
        io.set_capture_io_latencies(true);
        io.set_concurrent_read_io_limit(concurrent_read_io_limit);

        shared_state_t shared_state{io};
        if (auto bytes = shared_state.test_surface_available(); bytes < 1024) {
            std::stringstream ss;
            ss << "Storage used for test has " << bytes
               << " bytes allocated, this is too little to run the test. "
                  "Consider using --fill or --really-fill.";
            throw std::runtime_error(std::move(ss).str());
        }
        if (auto bytes = shared_state.test_surface_available();
            bytes < 100ULL * 1024 * 1024 * 1024) {
            std::cerr << "WARNING: Storage used for test has "
                      << (double(bytes) / 1024.0 / 1024.0 / 1024.0)
                      << " Gb allocated, it is recommended at least 100 Gb is "
                         "available for the random read test."
                      << std::endl;
        }

        struct statistics_t
        {
            uint32_t ops_per_sec{0};
            float mean_latency{0};
            float min_latency{0};
            float max_latency{0};
        } statistics;

        auto begin = std::chrono::steady_clock::now();
        auto print_statistics = [&] {
            auto const now = std::chrono::steady_clock::now();
            auto const elapsed =
                double(std::chrono::duration_cast<std::chrono::milliseconds>(
                           now - begin)
                           .count());
            statistics.ops_per_sec =
                uint32_t(1000.0 * double(shared_state.ops) / elapsed);
            statistics.mean_latency =
                float(double(shared_state.acc_ns) / double(shared_state.ops));
            statistics.min_latency = float(shared_state.min_ns);
            statistics.max_latency = float(shared_state.max_ns);
            std::cout << "\nTotal ops/sec: " << statistics.ops_per_sec
                      << " mean latency: " << statistics.mean_latency
                      << " min: " << statistics.min_latency
                      << " max: " << statistics.max_latency << std::endl;
        };

        if (!new_io_executor) {
            std::vector<connected_state_ptr_type> states;
            states.reserve(concurrent_io);
            for (size_t n = 0; n < concurrent_io; n++) {
                states.push_back(io.make_connected(
                    MONAD_ASYNC_NAMESPACE::read_single_buffer_sender({0, 0}, 0),
                    receiver_t{&shared_state}));
            }

            begin = std::chrono::steady_clock::now();
            for (auto &i : states) {
                MONAD_ASYNC_NAMESPACE::filled_read_buffer res;
                if (highest_io_priority) {
                    i->set_io_priority(
                        MONAD_ASYNC_NAMESPACE::erased_connected_operation::
                            io_priority::highest);
                }
                i->receiver().set_value(
                    i.get(),
                    MONAD_ASYNC_NAMESPACE::read_single_buffer_sender::
                        result_type{res});
            }
            io.set_eager_completions(eager_completions);
            shared_state.acc_ns = 0;
            shared_state.max_ns = 0;
            shared_state.min_ns = UINT64_MAX;
            std::chrono::seconds elapsed_secs(2);
            do {
                auto diff = std::chrono::duration_cast<std::chrono::seconds>(
                    std::chrono::steady_clock::now() - begin);
                if (diff > elapsed_secs) {
                    print_statistics();
                    elapsed_secs = diff;
                }
                io.poll_nonblocking(1);
                if (workload_us > 0) {
                    auto const begin2 = std::chrono::steady_clock::now();
                    do {
                        /* deliberately occupy the CPU fully */
                    }
                    while (std::chrono::steady_clock::now() - begin2 <
                           std::chrono::microseconds(workload_us));
                }
            }
            while (std::chrono::steady_clock::now() - begin <
                   std::chrono::seconds(duration_secs));
            shared_state.done = true;
            io.wait_until_done();
        }
        else {
            static auto const ticks_per_ns =
                (double)monad_async_ticks_per_second() / 1000000000.0;
            std::cout << "CPU ticks per second on this machine: "
                      << monad_async_ticks_per_second() << std::endl;
            {
                auto *desc =
                    (char *)to_result(
                        monad_async_executor_config_string(io.tr_executor()))
                        .value();
                std::cout << "Config: " << desc << "\n" << std::endl;
                free(desc);
            }

            struct io_state
            {
                monad_async_task_registered_io_buffer buffer;
                monad_async_io_status iostatus;

                constexpr io_state()
                    : buffer{}
                    , iostatus{}
                {
                }
            };

            std::vector<io_state> states(concurrent_io);
            std::chrono::seconds elapsed_secs(2);
            const struct timespec nowait = {0, 0};
            for (
                auto h = io.tr_launch_on_task_from_pool(
                    [&](monad_async_task task)
                        -> monad::async::result<intptr_t> {
                        if (highest_io_priority) {
                            to_result(monad_async_task_set_priorities(
                                          task,
                                          monad_async_priority_unchanged,
                                          monad_async_priority_high))
                                .value();
                        }
                        for (auto &i : states) {
                            io.tr_submit_request(
                                &i.iostatus,
                                task,
                                i.buffer,
                                MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE,
                                shared_state.add_op(0));
                        }
                        shared_state.acc_ns = 0;
                        shared_state.max_ns = 0;
                        shared_state.min_ns = UINT64_MAX;
                        begin = std::chrono::steady_clock::now();
                        do {
                            monad_async_io_status *completed = nullptr;
                            to_result(
                                monad_async_task_suspend_until_completed_io(
                                    &completed,
                                    task,
                                    monad_async_duration_infinite_non_cancelling))
                                .value();
                            auto *state =
                                (io_state *)((uintptr_t)completed -
                                             offsetof(io_state, iostatus));
                            to_result(
                                monad_async_task_release_registered_io_buffer(
                                    task, state->buffer.index))
                                .value();
                            io.tr_submit_request(
                                completed,
                                task,
                                state->buffer,
                                MONAD_ASYNC_NAMESPACE::DISK_PAGE_SIZE,
                                shared_state.add_op((
                                    uint64_t)((double)(completed
                                                           ->ticks_when_completed -
                                                       completed
                                                           ->ticks_when_initiated) /
                                              ticks_per_ns)));
                        }
                        while (!shared_state.done);
                        for (;;) {
                            monad_async_io_status *completed = nullptr;
                            if (to_result(
                                    monad_async_task_suspend_until_completed_io(
                                        &completed,
                                        task,
                                        monad_async_duration_infinite_non_cancelling))
                                    .value() == 0) {
                                break;
                            }
                            auto *state =
                                (io_state *)((uintptr_t)completed -
                                             offsetof(io_state, iostatus));
                            to_result(
                                monad_async_task_release_registered_io_buffer(
                                    task, state->buffer.index))
                                .value();
                            shared_state.add_op((
                                uint64_t)((double)(completed
                                                       ->ticks_when_completed -
                                                   completed
                                                       ->ticks_when_initiated) /
                                          ticks_per_ns));
                        }
                        return monad::async::success();
                    });
                h();) {
                auto diff = std::chrono::duration_cast<std::chrono::seconds>(
                    std::chrono::steady_clock::now() - begin);
                if (diff > elapsed_secs) {
                    print_statistics();
                    elapsed_secs = diff;
                }
                auto r = to_result(
                    monad_async_executor_run(io.tr_executor(), 1, &nowait));
                if (!r &&
                    r.assume_error() != monad::async::errc::stream_timeout) {
                    r.value();
                }
                if (workload_us > 0) {
                    auto const begin2 = std::chrono::steady_clock::now();
                    do {
                        /* deliberately occupy the CPU fully */
                    }
                    while (std::chrono::steady_clock::now() - begin2 <
                           std::chrono::microseconds(workload_us));
                }
                if (std::chrono::steady_clock::now() - begin >=
                    std::chrono::seconds(duration_secs)) {
                    shared_state.done = true;
                }
            }
        }
        print_statistics();
    }

    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
    }

    catch (const CLI::RequiredError &e) {
        std::cerr << "FATAL: " << e.what() << "\n\n";
        std::cerr << cli.help() << std::flush;
        return 1;
    }

    catch (std::exception const &e) {
        std::cerr << "FATAL: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}
