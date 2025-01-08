#pragma once

#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_mpt_db;

struct monad_mpt_db *monad_mpt_db_open_read_only(char const *const *, size_t);

void monad_mpt_db_destroy(struct monad_mpt_db *);

#ifdef __cplusplus
}
#endif
