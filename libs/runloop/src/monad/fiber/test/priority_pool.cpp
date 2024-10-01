#include "monad/core/spinlock.h"
#include <gtest/gtest.h>

#include <monad/async/cpp_helpers.hpp>
#include <monad/async/executor.h>
#include <monad/async/file_io.h>
#include <monad/async/task.h>
#include <monad/context/context_switcher.h>
#include <monad/core/c_result.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/priority_pool.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <atomic>
#include <chrono>
#include <cstdio>
#include <filesystem>
#include <latch>
#include <thread>
#include <vector>

#include <fcntl.h>

TEST(PriorityPool, benchmark)
{
    monad::fiber::PriorityPool ppool(
        (unsigned)std::thread::hardware_concurrency(),
        (unsigned)std::thread::hardware_concurrency() * 4);

    struct count_t
    {
        alignas(64) std::atomic<unsigned> count{0};
        std::byte padding_[56];
        count_t() = default;

        count_t(count_t const &) {}
    };

    static_assert(sizeof(count_t) == 64);

    std::vector<count_t> counts(std::thread::hardware_concurrency());
    std::atomic<size_t> countsidx{0};
    std::function<void()> task([&] {
        static thread_local size_t mycountidx =
            countsidx.fetch_add(1, std::memory_order_acq_rel);
        counts[mycountidx].count.fetch_add(1, std::memory_order_acq_rel);
    });
    auto sum = [&] {
        unsigned ret = 0;
        for (auto const &i : counts) {
            ret += i.count.load(std::memory_order_acquire);
        }
        return ret;
    };
    auto begin = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(1)) {
        ;
    }

    unsigned submitted = 0;
    begin = std::chrono::steady_clock::now();
    auto end = begin;
    for (;;) {
        for (size_t n = 0; n < 100000; n++) {
            ppool.submit(1, task);
        }
        submitted += 100000;
        end = std::chrono::steady_clock::now();
        if (end - begin >= std::chrono::seconds(5)) {
            break;
        }
    }
    while (sum() < submitted) {
        std::this_thread::yield();
    }
    end = std::chrono::steady_clock::now();
    double const ops_per_sec1 =
        1000000000.0 * double(submitted) /
        double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count());
    std::cout << "PriorityPool executed " << submitted << " ops which is "
              << ops_per_sec1 << " ops/sec." << std::endl;

    for (auto &i : counts) {
        EXPECT_GT(i.count.load(std::memory_order_acquire), 0);
        i.count.store(0, std::memory_order_release);
    }
    counts.resize(counts.size() + 1);
    begin = std::chrono::steady_clock::now();
    for (;;) {
        for (size_t n = 0; n < 100000; n++) {
            task();
        }
        end = std::chrono::steady_clock::now();
        if (end - begin >= std::chrono::seconds(5)) {
            break;
        }
    }
    auto const count = sum();
    double const ops_per_sec2 =
        1000000000.0 * double(count) /
        double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count());
    std::cout << "\nFor comparison, a single CPU core can execute " << count
              << " ops which is " << ops_per_sec2 << " ops/sec.\n";
    std::cout
        << "\nThis makes PriorityPool " << (ops_per_sec1 / ops_per_sec2)
        << " times faster than a single CPU core. Hardware concurrency is "
        << std::thread::hardware_concurrency() << std::endl;
}

TEST(PriorityPool, foreign_executor)
{
    monad::fiber::PriorityPool ppool(2, 4);
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 4;
    auto ex = monad::async::make_executor(ex_attr);

    std::latch latch1(1), latch2(1);
    std::function<void()> work([&] {
        auto *myfiber = monad_fiber_self();
        std::cout << "Work submitted to priority pool launches on fiber "
                  << myfiber << " thread " << gettid() << std::endl;

        struct shared1_t
        {
            monad_async_executor ex;
            std::latch &latch;
            monad_async_task task{};
        } shared1{ex.get(), latch1};
        myfiber->head.user_ptr = &shared1;

        // Detach myself from the fiber executor and attach myself to the
        // i/o executor
        struct shared2_t
        {
            monad::fiber::PriorityPool &ppool;
            monad_fiber_t saved_fiber{};
            monad_fiber_t *fiber{};
        } shared2{ppool};
        std::cout << "Fiber suspends and initiates transfer to i/o executor"
                  << std::endl;
        monad_fiber_suspend_save_detach_and_invoke(
            myfiber,
            &shared2.saved_fiber,
            +[](monad_context_task context_task) -> bool {
                auto *shared = (shared1_t *)context_task->user_ptr;

                // We are now running outside the context, which is suspended
                // Turn the 'naked' context into an async task
                shared->task = monad_async_task_from_foreign_context(
                    context_task, nullptr);
                std::cout << "Naked context attaches to i/o executor"
                          << std::endl;
                // Attach the task to the i/o executor. Attachment is thread
                // safe so this is fine. It'll resume when the i/o executor gets
                // round to it.
                to_result(
                    monad_async_task_attach(shared->ex, shared->task, nullptr))
                    .value();
                // Release the main thread to pump the i/o executor
                shared->latch.count_down();
                return true;
            });
        auto *task = shared1.task;
        std::cout << "Work is now running on i/o executor task " << task
                  << " thread " << gettid() << std::endl;
        // Do a few suspend and resume i/o on the i/o executor
        monad_async_file fh;
        for (;;) {
            char buffer[L_tmpnam];
            std::tmpnam(buffer);
            struct open_how how = {.flags = O_CREAT | O_EXCL, .mode = O_RDWR};
            auto r = to_result(
                monad_async_task_file_create(&fh, task, nullptr, buffer, &how));
            if (!r) {
                if (r.error() == monad::async::errc::file_exists) {
                    continue;
                }
                r.value();
            }
            std::filesystem::remove(buffer);
            break;
        }
        to_result(monad_async_task_file_destroy(task, fh)).value();

        // Detach myself from the i/o executor and attach myself to the
        // fiber executor
        std::cout << "i/o is complete, detaching from i/o executor and "
                     "resuming as a fiber"
                  << std::endl;
        task->derived.user_ptr = &shared2;
        to_result(
            monad_async_task_suspend_save_detach_and_invoke(
                task,
                nullptr,
                +[](monad_context_task context_task) -> monad_c_result {
                    auto *shared = (shared2_t *)context_task->user_ptr;
                    // We are now running outside the context, which is
                    // suspended
                    shared->fiber = monad_fiber_from_foreign_context(
                        context_task, &shared->saved_fiber);
                    std::cout
                        << "Naked context requests resume on priority pool"
                        << std::endl;
                    shared->ppool.resume(shared->fiber);
                    return monad_c_make_success(0);
                }))
            .value();
        MONAD_ASSERT(shared2.fiber == myfiber);
        std::cout << "Fiber " << myfiber
                  << " returns from i/o executor now running on thread "
                  << gettid() << std::endl;
        latch2.count_down();
        // Why do I need this here?
        MONAD_SPINLOCK_UNLOCK(&myfiber->lock);
    });
    // Submit work to priority pool
    ppool.submit(1, work);
    // Wait until work moves itself to the i/o executor
    std::cout << "Main loop awaits notification that i/o executor has had a "
                 "task attached to it"
              << std::endl;
    latch1.wait();
    std::cout << "Beginning pumping i/o executor" << std::endl;
    // This will exit when the task detaches itself from the i/o executor
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    // Wait until work moves itself back to priority pool
    std::cout << "Finished pumping i/o executor, await notification that work "
                 "has completed on the priority pool and exited"
              << std::endl;
    latch2.wait();
    std::cout << "Work has completed, destroying priority pool." << std::endl;
}
