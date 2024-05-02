#include <gtest/gtest.h>

#include "test_common.hpp"

#include "monad/async/context_switcher.h"

#include "monad/async/task.h"

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <utility>

/* Runtime pluggable context switchers:


   Testing none switcher ...
   Constructed and destroyed none switcher contexts at 4.26533e+07 ops/sec which
   is 23.4464 ns/op.


   Testing setjmp/longjmp switcher ...
   Constructed and destroyed setjmp/longjmp switcher contexts at 249754 ops/sec
   which is 4004.1 ns/op.


   Testing monad fiber switcher ...
   Constructed and destroyed monad fiber switcher contexts at 286373 ops/sec
   which is 3492.37 ns/op.

*/

TEST(context_switcher, works)
{
    auto cs_none = make_context_switcher(monad_async_context_switcher_none);
    auto cs_sjlj = make_context_switcher(monad_async_context_switcher_sjlj);
    auto cs_fiber = make_context_switcher(monad_async_context_switcher_fiber);

    std::vector<context_ptr> contexts(10000);
    auto test_creation_destruction = [&](monad_async_context_switcher switcher,
                                         char const *desc) {
        uint32_t ops = 0;
        monad_async_task_attr attr{.stack_size = 4096};
        std::cout << "\n\n   Testing " << desc << " ..." << std::endl;
        auto const begin = std::chrono::steady_clock::now();
        do {
            for (auto &i : contexts) {
                i = make_context(switcher, attr);
            }
            ops += (uint32_t)contexts.size();
        }
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(3));
        for (auto &i : contexts) {
            i.reset();
        }
        auto const end = std::chrono::steady_clock::now();
        std::cout
            << "   Constructed and destroyed " << desc << " contexts at "
            << (1000.0 * double(ops) /
                double(std::chrono::duration_cast<std::chrono::milliseconds>(
                           end - begin)
                           .count()))
            << " ops/sec which is "
            << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count()) /
                double(ops))
            << " ns/op." << std::endl;
    };
    test_creation_destruction(cs_none.get(), "none switcher");
    test_creation_destruction(cs_sjlj.get(), "setjmp/longjmp switcher");
    test_creation_destruction(cs_fiber.get(), "monad fiber switcher");
}
