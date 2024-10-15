#include <monad/statesync/statesync_version.h>

bool monad_statesync_compatible(uint32_t const version)
{
    static_assert(MONAD_STATESYNC_VERSION == 1, "modify on version bump");
    return version <= MONAD_STATESYNC_VERSION && version >= 1;
}
