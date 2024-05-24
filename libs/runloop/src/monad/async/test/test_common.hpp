#pragma once

#include "monad/async/cpp_helpers.hpp"

using namespace monad::async;
#define CHECK_RESULT2(unique, ...)                                             \
    {                                                                          \
        auto unique = (__VA_ARGS__);                                           \
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(unique)) {                        \
            throw_exception(unique);                                           \
        }                                                                      \
    }
#define CHECK_RESULT(...) CHECK_RESULT2(MONAD_ASYNC_UNIQUE_NAME, __VA_ARGS__)
