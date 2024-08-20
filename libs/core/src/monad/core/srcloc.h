#pragma once

typedef struct monad_source_location monad_source_location_t;

/// A pure C structure compatible with C++20's std::source_location
struct monad_source_location
{
    char const *function_name;
    char const *file_name;
    unsigned line;
    unsigned column;
};
