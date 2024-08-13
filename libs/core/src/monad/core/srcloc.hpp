#pragma once

#include <monad/config.hpp>
#include <monad/core/srcloc.h>
#include <source_location>

MONAD_NAMESPACE_BEGIN

constexpr monad_source_location_t make_srcloc(const std::source_location &s) {
    return monad_source_location_t {
        .function_name = s.function_name(),
        .file_name = s.file_name(),
        .line = s.line(),
        .column = s.column()
    };
}

MONAD_NAMESPACE_END