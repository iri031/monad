#include <err.h>
#include <errno.h>
#include <getopt.h>
#include <libgen.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <sysexits.h>

#include <monad/context/context_switcher.h>
#include <monad/core/likely.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/fiber_semaphore.h>
#include <monad/fiber/run_queue.h>
#include <monad/util/parse_util.h>

// TODO(ken): make constexpr
//   https://github.com/monad-crypto/monad-internal/issues/498
static uintptr_t const KIBI_MASK = (1UL << 10) - 1;
static uint64_t const NANOS_PER_SECOND = 1'000'000'000ULL;

static size_t g_fiber_stack_size = 1UL << 17; // 128 KiB
static time_t g_benchmark_seconds = 10;
static size_t g_run_queue_fibers = 256;

enum long_only_option
{
    LO_RUN_QUEUE_FIBERS
};

// clang-format: off
// @formatter:off
static struct option longopts[] = {
    {.name = "list", .has_arg = 0, .flag = nullptr, .val = 'L'},
    {.name = "list-switchers", .has_arg = 0, .flag = nullptr, .val = 'W'},
    {.name = "switcher", .has_arg = 1, .flag = nullptr, .val = 'w'},
    {.name = "stack_shift", .has_arg = 1, .flag = nullptr, .val = 's'},
    {.name = "time", .has_arg = 1, .flag = nullptr, .val = 't'},
    {.name = "rq-fibers",
     .has_arg = 1,
     .flag = nullptr,
     .val = LO_RUN_QUEUE_FIBERS},
    {.name = "help", .has_arg = 1, .flag = nullptr, .val = 'h'},
    {}};
// @formatter:on
// clang-format: on

extern char const *__progname;

static void usage(FILE *out)
{
    fprintf(
        out,
        "%s: [-LWh] [-w <switcher>] [-t <sec>] [-s <shift>] [--rq-fibers <#>] [benchmark...]\n",
        __progname);
}

static int64_t to_nanos(struct timespec ts)
{
    return ts.tv_sec * NANOS_PER_SECOND + ts.tv_nsec;
}

static time_t elapsed_nanos(struct timespec start, struct timespec end)
{
    return to_nanos(end) - to_nanos(start);
}

static time_t elapsed_seconds(struct timespec start, struct timespec end)
{
    return elapsed_nanos(start, end) / NANOS_PER_SECOND;
}

#define BENCH_DIE(...)                                                         \
    fprintf(                                                                   \
        stderr,                                                                \
        "FATAL at %s@%s:%d\n",                                                 \
        __PRETTY_FUNCTION__,                                                   \
        basename(__FILE__),                                                    \
        __LINE__);                                                             \
    if (errno == 0) {                                                          \
        errx(1, __VA_ARGS__);                                                  \
    }                                                                          \
    else {                                                                     \
        err(1, __VA_ARGS__);                                                   \
    }

#define CHECK_Z(X)                                                             \
    do {                                                                       \
        if (MONAD_UNLIKELY((X) != 0)) {                                        \
            errno = (X);                                                       \
            BENCH_DIE(#X " != 0");                                             \
        }                                                                      \
    }                                                                          \
    while (0)

#define ASSERT_EQ(X, Y)                                                        \
    do {                                                                       \
        if (MONAD_UNLIKELY((X) != (Y))) {                                      \
            errno = 0;                                                         \
            BENCH_DIE("assert failed: " #X " == " #Y);                         \
        }                                                                      \
    }                                                                          \
    while (0)

struct benchmark;

static void switch_benchmark(struct benchmark const *);
static void run_queue_benchmark(struct benchmark const *);
static void channel_benchmark(struct benchmark const *);
static void semaphore_benchmark(struct benchmark const *);

static struct benchmark
{
    char const *name;
    char const *description;
    void (*func)(struct benchmark const *);
} g_bench_table[] = {
    {.name = "switch",
     .description = "performance of fiber context switch",
     .func = switch_benchmark},
    {.name = "rq",
     .description = "performance of run queue",
     .func = run_queue_benchmark},
    {.name = "chan",
     .description = "performance of fiber channels",
     .func = channel_benchmark},
    {.name = "sem",
     .description = "performance of fiber semaphores",
     .func = semaphore_benchmark}};

static const struct benchmark *const g_bench_table_end =
    g_bench_table + sizeof(g_bench_table) / sizeof(struct benchmark);

static struct context_switcher_meta
{
    char const *name;
    monad_context_switcher_impl const *impl;
} g_context_switcher_table[] = {
    {.name = "none", .impl = &monad_context_switcher_none},
    {.name = "sjlj", .impl = &monad_context_switcher_sjlj},
    {.name = "fcontext", .impl = &monad_context_switcher_fcontext}};

static const struct context_switcher_meta *const g_context_switcher_table_end =
    g_context_switcher_table +
    sizeof(g_context_switcher_table) / sizeof(struct context_switcher_meta);

int parse_options(int argc, char **argv)
{
    int ch;
    bool option_found;
    monad_c_result mcr;
    struct context_switcher_meta *csm;

    while ((ch = getopt_long(argc, argv, "w:s:t:LWh", longopts, nullptr)) !=
           -1) {
        switch (ch) {
        case 'L':
            for (struct benchmark *b = g_bench_table; b != g_bench_table_end;
                 ++b) {
                fprintf(stdout, "%s:\t%s\n", b->name, b->description);
            }
            exit(0);

        case 'W':
            fprintf(stdout, "%s", g_context_switcher_table->name);
            for (csm = g_context_switcher_table + 1;
                 csm != g_context_switcher_table_end;
                 ++csm) {
                fprintf(stdout, " %s", csm->name);
            }
            fprintf(stdout, "\n");
            exit(0);

        case 'w':
            option_found = false;
            for (csm = g_context_switcher_table;
                 csm != g_context_switcher_table_end;
                 ++csm) {
                if (strcmp(csm->name, optarg) == 0) {
                    atomic_store_explicit(
                        &g_monad_fiber_default_context_switcher_impl,
                        csm->impl,
                        memory_order_release);
                    option_found = true;
                    break;
                }
            }
            if (!option_found) {
                errx(
                    EX_USAGE,
                    "%s is not a valid type of context switcher",
                    optarg);
            }
            break;

        case 's':
            mcr = monad_strtonum(optarg, 10, 30);
            if (MONAD_FAILED(mcr)) {
                monad_errc(
                    1, mcr.error, "bad -s|--stack-shift value '%s'", optarg);
            }
            g_fiber_stack_size = 1UL << (unsigned)mcr.value;
            break;

        case 't':
            mcr = monad_strtonum(optarg, 1, 300);
            if (MONAD_FAILED(mcr)) {
                monad_errc(1, mcr.error, "bad -t|--time value '%s'", optarg);
            }
            g_benchmark_seconds = mcr.value;
            break;

        case LO_RUN_QUEUE_FIBERS:
            mcr = monad_strtonum(optarg, 1, 1L << 20);
            if (MONAD_FAILED(mcr)) {
                monad_errc(1, mcr.error, "bad --rq-fibers value '%s'", optarg);
            }
            g_run_queue_fibers = mcr.value;
            break;

        case 'h':
            usage(stdout);
            exit(0);

        case '?':
            [[fallthrough]];
        default:
            usage(stderr);
            exit(EX_USAGE);
        }
    }

    return optind;
}

static monad_c_result yield_forever(monad_fiber_args_t mfa)
{
    atomic_bool *const done = (atomic_bool *)mfa.arg[0];
    uintptr_t y = 0;
    while (!atomic_load_explicit(done, memory_order_relaxed)) {
        monad_fiber_yield(monad_c_make_success(y++));
    }
    return monad_c_make_success(y);
}

struct channel_test_data
{
    atomic_bool done;
    monad_fiber_channel_t channel_a;
    monad_fiber_channel_t channel_b;
};

static monad_c_result channel_a_loop(monad_fiber_args_t mfa)
{
    monad_fiber_msghdr_t *msghdr;
    struct channel_test_data *const test_data =
        (struct channel_test_data *)mfa.arg[0];
    intptr_t count = 0;
    do {
        msghdr = monad_fiber_channel_pop(
            &test_data->channel_a, MONAD_FIBER_PRIO_NO_CHANGE);
        ++count;
        monad_fiber_channel_push(&test_data->channel_b, msghdr);
    }
    while (!atomic_load_explicit(&test_data->done, memory_order_acquire));
    return monad_c_make_success(count);
}

static monad_c_result channel_b_loop(monad_fiber_args_t mfa)
{
    monad_fiber_msghdr_t msghdr;
    monad_fiber_msghdr_t *m;
    struct channel_test_data *const test_data =
        (struct channel_test_data *)mfa.arg[0];
    intptr_t count = 0;
    monad_fiber_msghdr_init(
        &msghdr, (struct iovec){.iov_base = &count, .iov_len = sizeof count});
    m = &msghdr;
    do {
        monad_fiber_channel_push(&test_data->channel_a, m);
        ++count;
        m = monad_fiber_channel_pop(
            &test_data->channel_b, MONAD_FIBER_PRIO_NO_CHANGE);
    }
    while (!atomic_load_explicit(&test_data->done, memory_order_acquire));
    return monad_c_make_success(count);
}

struct semaphore_test_data
{
    atomic_bool done;
    monad_fiber_semaphore_t sem_a;
    monad_fiber_semaphore_t sem_b;
};

static monad_c_result sem_a_loop(monad_fiber_args_t mfa)
{
    struct semaphore_test_data *const test_data =
        (struct semaphore_test_data *)mfa.arg[0];
    intptr_t count = 0;
    do {
        monad_fiber_semaphore_acquire(
            &test_data->sem_a, MONAD_FIBER_PRIO_NO_CHANGE);
        ++count;
        monad_fiber_semaphore_release(&test_data->sem_b, 1);
    }
    while (!atomic_load_explicit(&test_data->done, memory_order_acquire));
    return monad_c_make_success(count);
}

static monad_c_result sem_b_loop(monad_fiber_args_t mfa)
{
    struct semaphore_test_data *const test_data =
        (struct semaphore_test_data *)mfa.arg[0];
    intptr_t count = 0;
    do {
        monad_fiber_semaphore_release(&test_data->sem_a, 1);
        ++count;
        monad_fiber_semaphore_acquire(
            &test_data->sem_b, MONAD_FIBER_PRIO_NO_CHANGE);
    }
    while (!atomic_load_explicit(&test_data->done, memory_order_acquire));
    return monad_c_make_success(count);
}

static void switch_benchmark(struct benchmark const *self)
{
    monad_fiber_t *fiber;
    monad_fiber_suspend_info_t suspend_info;
    atomic_bool done;
    struct timespec start_time;
    struct timespec now;
    monad_fiber_attr_t fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};

    CHECK_Z(monad_fiber_create(&fiber_attr, &fiber));
    CHECK_Z(monad_fiber_set_function(
        fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        yield_forever,
        (monad_fiber_args_t){.arg = {(uintptr_t)&done}}));

    atomic_init(&done, false);
    (void)clock_gettime(CLOCK_REALTIME, &start_time);
    do {
        CHECK_Z(monad_fiber_run(fiber, &suspend_info));
        ASSERT_EQ(monad_result_has_value(suspend_info.eval), true);
        if ((suspend_info.eval.value & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            (void)clock_gettime(CLOCK_REALTIME, &now);
            atomic_store_explicit(
                &done,
                elapsed_seconds(start_time, now) >= g_benchmark_seconds,
                memory_order_release);
        }
    }
    while (!done);

    CHECK_Z(monad_fiber_run(fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    monad_fiber_destroy(fiber);

    uintptr_t const context_switch_count = suspend_info.eval.value + 1;
    double const nanos_per_switch =
        (double)(g_benchmark_seconds * NANOS_PER_SECOND) /
        (double)context_switch_count;
    fprintf(
        stdout,
        "%s:\tsingle core context switch rate: %lu sw/s, %.1f ns/sw\n",
        self->name,
        context_switch_count / g_benchmark_seconds,
        nanos_per_switch);
}

static void run_queue_benchmark(struct benchmark const *self)
{
    monad_fiber_t **fibers;
    monad_fiber_t *next_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_run_queue_t *rq;
    atomic_bool done;
    struct timespec start_time;
    struct timespec now;
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};
    size_t run_count = 0;

    atomic_init(&done, false);
    CHECK_Z(monad_run_queue_create(nullptr, g_run_queue_fibers, &rq));
    fibers = calloc(g_run_queue_fibers, sizeof *fibers);
    for (size_t f = 0; f < g_run_queue_fibers; ++f) {
        CHECK_Z(monad_fiber_create(&fiber_attr, &fibers[f]));
        CHECK_Z(monad_fiber_set_function(
            fibers[f],
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            (monad_fiber_args_t){.arg = {(uintptr_t)&done}}));
        CHECK_Z(monad_run_queue_try_push(rq, fibers[f]));
    }

    (void)clock_gettime(CLOCK_REALTIME, &start_time);
    do {
        next_fiber = monad_run_queue_try_pop(rq);
        (void)monad_fiber_run(next_fiber, nullptr);
        if ((++run_count & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            (void)clock_gettime(CLOCK_REALTIME, &now);
            atomic_store_explicit(
                &done,
                now.tv_sec - start_time.tv_sec == g_benchmark_seconds,
                memory_order_release);
        }
    }
    while (!done);

    while (!monad_run_queue_is_empty(rq)) {
        next_fiber = monad_run_queue_try_pop(rq);
        monad_fiber_run(next_fiber, &suspend_info);
        ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    }

    monad_run_queue_destroy(rq);
    for (size_t f = 0; f < g_run_queue_fibers; ++f) {
        monad_fiber_destroy(fibers[f]);
    }
    free(fibers);

    double const nanos_per_run_cycle =
        (g_benchmark_seconds * 1'000'000'000.0) / (double)run_count;
    fprintf(
        stdout,
        "%s:\tsingle core run cycle rate: %lu r/s, %.1f ns/r\n",
        self->name,
        run_count / g_benchmark_seconds,
        nanos_per_run_cycle);
}

static void channel_benchmark(struct benchmark const *self)
{
    monad_fiber_t *fibers[2];
    monad_fiber_t *next_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_run_queue_t *rq;
    struct channel_test_data test_data;
    struct timespec start_time;
    struct timespec now;
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};
    monad_fiber_ffunc_t *const fiber_funcs[] = {channel_a_loop, channel_b_loop};
    size_t run_count = 0;
    size_t wakeup_count = 0;

    atomic_init(&test_data.done, false);
    monad_fiber_channel_init(&test_data.channel_a);
    monad_fiber_channel_init(&test_data.channel_b);
    CHECK_Z(monad_run_queue_create(nullptr, 2, &rq));
    for (size_t f = 0; f < 2; ++f) {
        monad_fiber_create(&fiber_attr, &fibers[f]);
        CHECK_Z(monad_fiber_set_function(
            fibers[f],
            MONAD_FIBER_PRIO_HIGHEST + f,
            fiber_funcs[f],
            (monad_fiber_args_t){.arg=(uintptr_t)&test_data}));
        CHECK_Z(monad_run_queue_try_push(rq, fibers[f]));
    }

    (void)clock_gettime(CLOCK_REALTIME, &start_time);
    do {
        next_fiber = monad_run_queue_try_pop(rq);
        (void)monad_fiber_run(next_fiber, nullptr);
        if ((++run_count & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            (void)clock_gettime(CLOCK_REALTIME, &now);
            atomic_store_explicit(
                &test_data.done,
                now.tv_sec - start_time.tv_sec == g_benchmark_seconds,
                memory_order_release);
        }
    }
    while (!test_data.done);

    while (!monad_run_queue_is_empty(rq)) {
        next_fiber = monad_run_queue_try_pop(rq);
        monad_fiber_run(next_fiber, &suspend_info);
        if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
            wakeup_count += suspend_info.eval.value;
            monad_fiber_destroy(next_fiber);
        }
    }

    monad_run_queue_destroy(rq);

    double const nanos_per_wakeup =
        (g_benchmark_seconds * 1'000'000'000.0) / (double)wakeup_count;
    fprintf(
        stdout,
        "%s:\tsingle core channel wakeup rate: %lu w/s, %.1f ns/w\n",
        self->name,
        wakeup_count / g_benchmark_seconds,
        nanos_per_wakeup);
}

static void semaphore_benchmark(struct benchmark const *self)
{
    monad_fiber_t *fibers[2];
    monad_fiber_t *next_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_run_queue_t *rq;
    struct semaphore_test_data test_data;
    struct timespec start_time;
    struct timespec now;
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};
    monad_fiber_ffunc_t *const fiber_funcs[] = {sem_a_loop, sem_b_loop};
    size_t run_count = 0;
    size_t wakeup_count = 0;

    atomic_init(&test_data.done, false);
    monad_fiber_semaphore_init(&test_data.sem_a);
    monad_fiber_semaphore_init(&test_data.sem_b);
    CHECK_Z(monad_run_queue_create(nullptr, 2, &rq));
    for (size_t f = 0; f < 2; ++f) {
        monad_fiber_create(&fiber_attr, &fibers[f]);
        CHECK_Z(monad_fiber_set_function(
            fibers[f],
            MONAD_FIBER_PRIO_HIGHEST + f,
            fiber_funcs[f],
            (monad_fiber_args_t){.arg=(uintptr_t)&test_data}));
        CHECK_Z(monad_run_queue_try_push(rq, fibers[f]));
    }

    (void)clock_gettime(CLOCK_REALTIME, &start_time);
    do {
        next_fiber = monad_run_queue_try_pop(rq);
        (void)monad_fiber_run(next_fiber, nullptr);
        if ((++run_count & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            (void)clock_gettime(CLOCK_REALTIME, &now);
            atomic_store_explicit(
                &test_data.done,
                now.tv_sec - start_time.tv_sec == g_benchmark_seconds,
                memory_order_release);
        }
    }
    while (!test_data.done);

    while (!monad_run_queue_is_empty(rq)) {
        next_fiber = monad_run_queue_try_pop(rq);
        monad_fiber_run(next_fiber, &suspend_info);
        if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
            wakeup_count += suspend_info.eval.value;
            monad_fiber_destroy(next_fiber);
        }
    }

    monad_run_queue_destroy(rq);

    double const nanos_per_wakeup =
        (g_benchmark_seconds * 1'000'000'000.0) / (double)wakeup_count;
    fprintf(
        stdout,
        "%s:\tsingle core semaphore wakeup rate: %lu w/s, %.1f ns/w\n",
        self->name,
        wakeup_count / g_benchmark_seconds,
        nanos_per_wakeup);
}

int main(int argc, char **argv)
{
    char const *pos_arg;
    struct benchmark *bench;
    int next_pos_arg_idx = parse_options(argc, argv);

    if (next_pos_arg_idx == argc) {
        // Not specifying any benchmark runs all of them
        for (bench = g_bench_table; bench != g_bench_table_end; ++bench) {
            bench->func(bench);
            fflush(stdout);
        }
    }
    while (next_pos_arg_idx != argc) {
        // If there are position arguments, run the benchmark named by the
        // argument; run with -L to see a list
        pos_arg = argv[next_pos_arg_idx++];
        for (bench = g_bench_table; bench != g_bench_table_end; ++bench) {
            if (strcmp(pos_arg, bench->name) == 0) {
                bench->func(bench);
                fflush(stdout);
                break;
            }
        }
        if (bench == g_bench_table_end) {
            warnx("benchmark %s not found", pos_arg);
        }
    }

    return 0;
}
