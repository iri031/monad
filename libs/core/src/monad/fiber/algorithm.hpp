#pragma once

#include <monad/core/assert.h>
#include <monad/core/result.hpp>
#include <monad/fiber/config.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <boost/fiber/future/promise.hpp>
#pragma GCC diagnostic pop

#include <boost/outcome/success_failure.hpp>

#include <span>

MONAD_FIBER_NAMESPACE_BEGIN

template <class Output1, class F, class Output2>
Result<void>
map(std::span<boost::fibers::promise<Result<Output1>>> const promises, F &&f,
    std::span<Output2> const output)
{
    MONAD_ASSERT(promises.size() == output.size());
    std::optional<Result<void>> error;
    for (unsigned i = 0; i < promises.size(); ++i) {
        auto future = promises[i].get_future();
        future.wait();
        auto result = future.get();
        if (result.has_error()) {
            if (!error.has_value()) {
                error = std::move(result.error());
            }
        }
        else {
            output[i] = f(std::move(result.assume_value()));
        }
    }
    return error.has_value() ? std::move(error.value()) : outcome::success();
}

MONAD_FIBER_NAMESPACE_END
