#pragma once

typedef struct monad_source_location monad_source_location_t;

struct monad_source_location {
    const char *function_name;
    const char *file_name;
    unsigned line;
    unsigned column;
};
