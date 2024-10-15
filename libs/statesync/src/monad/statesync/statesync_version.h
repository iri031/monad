#pragma once

#include <monad/statesync/statesync_messages.h>

#ifdef __cplusplus
extern "C"
{
#endif

constexpr uint32_t MONAD_STATESYNC_VERSION = 1;

bool monad_statesync_compatible(uint32_t version);

#ifdef __cplusplus
}
#endif
