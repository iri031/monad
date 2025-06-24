#include <monad/lru/clock.hpp>
#include <monad/lru/lru_cache.hpp>
#include <monad/lru/static_lru_cache.hpp>
#include <monad/util/zipfian.hpp>

#include <algorithm>
#include <iostream>
#include <random>
#include <vector>

#include <nanobench.h>

// resolving path's in the prefix materialises nodes creating dependencies
// lru captures this history well via recency, but doesn't account for the
// popularity/frequency of a node-path, keys are uniformly distributed
// temporal locality is only granted via storage slot access patterns.

// read-heavy
// read-write
// loop
// scan
// zipf dist

using LruCache = monad::LruCache<int, int>;
using ClockCache = monad::ClockReplacer<int, int>;

// cache's first five levels: 16 ** 5 = 1_048_576 // guesstimate num_keys
static constexpr int POP = 1048576;

void access_lru_benchmark()
{
    constexpr size_t N_SAMPLES = 1000;
    auto const populations = {10000, POP};
    auto const fills = {0.5, 0.75, 1.0};

    for (auto population : populations) {
        for (double fill : fills) {
            auto title = "LRU N=" + std::to_string(population) +
                         "fill=" + std::to_string(fill);

            ankerl::nanobench::Bench bench;
            bench.performanceCounters(true);

            bench.run(title + " cap " + std::to_string(population), [&] {
                auto const pop_size = static_cast<size_t>(population);
                LruCache cache(pop_size);
                LruCache::ConstAccessor acc;

                std::vector<size_t> samples(pop_size);
                for (size_t i = 0; i < pop_size; i++) {
                    samples[i] = i;
                }

                std::mt19937 rng(1);
                std::shuffle(samples.begin(), samples.end(), rng);

                auto pop = static_cast<double>(population);
                samples.resize(static_cast<size_t>(fill * pop));

                for (auto s : samples) {
                    cache.insert(static_cast<int>(s), static_cast<int>(s));
                }

                double count = 0;
                ankerl::nanobench::doNotOptimizeAway(count);

                for (size_t i = 0; i < N_SAMPLES; i++) {
                    count += cache.find(acc, static_cast<int>(i)) ? 1 : 0;
                }

                return count;
            });
        }
    }
}

void access_clock_benchmark()
{
    constexpr size_t N_SAMPLES = 1000;
    auto populations = {10000, POP};
    auto fills = {0.5, 0.75, 1.0};

    for (auto population : populations) {
        for (double fill : fills) {
            auto title = "atomic clock N=" + std::to_string(population) +
                         " fill=" + std::to_string(fill);

            ankerl::nanobench::Bench bench;
            bench.performanceCounters(true);

            bench.run(title + std::to_string(population), [&] {
                auto const pop_size = static_cast<size_t>(population);
                ClockCache cache(pop_size);

                std::vector<size_t> samples(pop_size);
                for (size_t i = 0; i < pop_size; i++) {
                    samples[i] = i;
                }

                std::mt19937 rng(1);
                std::shuffle(samples.begin(), samples.end(), rng);

                auto pop = static_cast<double>(population);
                samples.resize(static_cast<size_t>(fill * pop));

                for (auto p : samples) {
                    cache.insert(static_cast<int>(p), static_cast<int>(p));
                }

                size_t count = 0;
                ankerl::nanobench::doNotOptimizeAway(count);

                for (size_t i = 0; i < N_SAMPLES; i++) {
                    count += cache.find(static_cast<int>(i)) ? 1 : 0;
                }

                return count;
            });
        }
    }
}

void clock_zipf_benchmark()
{
    constexpr size_t N_SAMPLES = 1000;
    auto populations = {10000.0, static_cast<double>(POP)};
    auto fills = {0.5, 0.75};
    auto capacity_ratios = {0.05, 0.1, 0.15};

    for (auto pop : populations) {
        for (auto fill : fills) {
            std::string benchmark_name =
                "atomic Clock Zipf N=" +
                std::to_string(static_cast<size_t>(pop)) +
                " Fill=" + std::to_string(fill);

            for (auto cap_ratio : capacity_ratios) {
                size_t capacity = static_cast<size_t>(pop * cap_ratio);
                auto run = benchmark_name + " cap " + std::to_string(capacity);

                ankerl::nanobench::Bench bench;
                bench.performanceCounters(true);

                bench.run(run, [&] {
                    std::mt19937 rng(1);
                    monad::ZipfDistribution dist(pop, fill);

                    ClockCache cache(capacity);

                    for (size_t i = 0; i < static_cast<size_t>(pop); i++) {
                        auto sample = dist.sample(rng);
                        cache.insert(sample, sample);
                    }

                    double hits = 0;
                    double misses = 0;

                    for (auto i = 0; i < static_cast<int>(N_SAMPLES); i++) {
                        auto sample = dist.sample(rng);

                        if (cache.find(sample)) {
                            hits++;
                        }
                        else {
                            cache.insert(sample, sample);
                            misses++;
                        }
                    }

                    return std::make_pair(hits, misses);
                });
            }
        }
    }
}

void lru_zipf_benchmark()
{
    constexpr size_t N_SAMPLES = 1000;
    auto populations = {10000.0, static_cast<double>(POP)};
    auto fills = {0.5, 0.75};
    auto capacity_ratios = {0.05, 0.1, 0.15};

    for (auto pop : populations) {
        for (auto fill : fills) {
            std::string benchmark_name =
                "thread-safe lru Zipf N=" +
                std::to_string(static_cast<size_t>(pop)) +
                " Fill=" + std::to_string(fill);

            for (auto cap_ratio : capacity_ratios) {
                size_t capacity = static_cast<size_t>(pop * cap_ratio);
                auto run = benchmark_name + " cap " + std::to_string(capacity);

                ankerl::nanobench::Bench bench;
                bench.performanceCounters(true);

                bench.run(run, [&] {
                    std::mt19937 rng(1);
                    monad::ZipfDistribution dist(pop, fill);

                    LruCache cache(capacity);
                    LruCache::ConstAccessor acc;

                    for (size_t i = 0; i < static_cast<size_t>(pop); i++) {
                        auto sample = dist.sample(rng);
                        cache.insert(sample, sample);
                    }

                    double hits = 0;
                    double misses = 0;

                    for (auto i = 0; i < static_cast<int>(N_SAMPLES); i++) {
                        auto sample = dist.sample(rng);

                        if (cache.find(acc, sample)) {
                            hits++;
                        }
                        else {
                            cache.insert(sample, sample);
                            misses++;
                        }
                    }

                    /*
             auto hit_rate = hits / (hits + misses);

             std::cout << "\n"
                       << run << " - Hits: " << hits
                       << ", Misses: " << misses
                       << ", Hit Rate: " << hit_rate << "\n";
             */

                    return std::make_pair(hits, misses);
                });
            }
        }
    }
}

// concurrent//throughput bench

void lru_zipf_benchmark_parallel()
{
    constexpr size_t N_SAMPLES = 1000;
    auto populations = {10000.0, static_cast<double>(POP)};
    auto fills = {0.5, 0.75};
    auto capacity_ratios = {0.05, 0.1, 0.15};
    constexpr size_t NUM_THREADS = 4;

    for (auto pop : populations) {
        for (auto fill : fills) {
            std::string benchmark_name =
                "thread-safe lru Zipf N=" +
                std::to_string(static_cast<size_t>(pop)) +
                " Fill=" + std::to_string(fill);

            for (auto cap_ratio : capacity_ratios) {
                size_t capacity = static_cast<size_t>(pop * cap_ratio);
                auto run = benchmark_name + " cap " + std::to_string(capacity);

                ankerl::nanobench::Bench bench;
                bench.performanceCounters(true);

                bench.run(run, [&] {
                    LruCache cache(capacity);

                    // Pre-fill the cache
                    {
                        std::mt19937 rng_seed(1);
                        monad::ZipfDistribution dist(pop, fill);
                        for (size_t i = 0; i < static_cast<size_t>(pop); i++) {
                            auto sample = dist.sample(rng_seed);
                            cache.insert(sample, sample);
                        }
                    }
                    auto task = [&](std::atomic<double> &hits,
                                    std::atomic<double> &misses,
                                    unsigned int seed) {
                        std::mt19937 rng(seed);
                        monad::ZipfDistribution dist(pop, fill);
                        LruCache::ConstAccessor acc;
                        size_t local_samples = N_SAMPLES / NUM_THREADS;

                        for (size_t i = 0; i < local_samples; i++) {
                            auto sample = dist.sample(rng);
                            if (cache.find(acc, sample)) {
                                hits.fetch_add(1, std::memory_order_relaxed);
                            }
                            else {
                                cache.insert(sample, sample);
                                misses.fetch_add(1, std::memory_order_relaxed);
                            }
                        }
                    };

                    std::atomic<double> hits{0};
                    std::atomic<double> misses{0};

                    std::vector<std::thread> threads;

                    for (size_t i = 0; i < NUM_THREADS; i++) {
                        threads.emplace_back(
                            task,
                            std::ref(hits),
                            std::ref(misses),
                            static_cast<unsigned int>(i + 1234));
                    }

                    for (auto &t : threads) {
                        t.join();
                    }

                    return std::make_pair(hits.load(), misses.load());
                });
            }
        }
    }
}

void clock_zipf_benchmark_parallel()
{
    constexpr size_t N_SAMPLES = 1000;
    auto populations = {10000.0, static_cast<double>(POP)};
    auto fills = {0.5, 0.75};
    auto capacity_ratios = {0.05, 0.1, 0.15};
    constexpr size_t NUM_THREADS = 4;

    for (auto pop : populations) {
        for (auto fill : fills) {
            std::string benchmark_name =
                "atomic clock Zipf N=" +
                std::to_string(static_cast<size_t>(pop)) +
                " Fill=" + std::to_string(fill);

            for (auto cap_ratio : capacity_ratios) {
                size_t capacity = static_cast<size_t>(pop * cap_ratio);
                auto run = benchmark_name + " cap " + std::to_string(capacity);

                ankerl::nanobench::Bench bench;
                bench.performanceCounters(true);

                bench.run(run, [&] {
                    ClockCache cache(capacity);

                    // Pre-fill the cache
                    {
                        std::mt19937 rng_seed(1);
                        monad::ZipfDistribution dist(pop, fill);
                        for (size_t i = 0; i < static_cast<size_t>(pop); i++) {
                            auto sample = dist.sample(rng_seed);
                            cache.insert(sample, sample);
                        }
                    }

                    // Thread function for parallel hits/misses measurement
                    auto task = [&](std::atomic<double> &hits,
                                    std::atomic<double> &misses,
                                    unsigned int seed) {
                        std::mt19937 rng(seed);
                        monad::ZipfDistribution dist(pop, fill);

                        // Each thread works on a portion of N_SAMPLES
                        size_t local_samples = N_SAMPLES / NUM_THREADS;
                        for (size_t i = 0; i < local_samples; i++) {
                            auto sample = dist.sample(rng);
                            if (cache.find(sample)) {
                                hits.fetch_add(1, std::memory_order_relaxed);
                            }
                            else {
                                cache.insert(sample, sample);
                                misses.fetch_add(1, std::memory_order_relaxed);
                            }
                        }
                    };

                    std::atomic<double> hits{0};
                    std::atomic<double> misses{0};
                    std::vector<std::thread> threads;

                    // Launch threads
                    for (size_t i = 0; i < NUM_THREADS; i++) {
                        threads.emplace_back(
                            task,
                            std::ref(hits),
                            std::ref(misses),
                            static_cast<unsigned int>(i + 1234));
                    }

                    for (auto &t : threads) {
                        t.join();
                    }

                    return std::make_pair(hits.load(), misses.load());
                });
            }
        }
    }
}

int main()
{
    // access_lru_benchmark();
    // access_clock_benchmark();

    // lru_zipf_benchmark_parallel();
    // clock_zipf_benchmark_parallel();

    return 0;
}
