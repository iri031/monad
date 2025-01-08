#include <monad/core/intx.h>

#include <intx/intx.hpp>

#include <cstring>
#include <stdexcept>

int monad_uint256_from_string(
    char const *const from, unsigned char (*to)[MONAD_UINT256_SIZE])
{
    try {
        auto const src = intx::from_string<::intx::uint256>(from);
        std::memcpy(to, intx::as_bytes(src), MONAD_UINT256_SIZE);
    }
    catch (std::invalid_argument const &) {
        return -1;
    }
    catch (std::out_of_range const &) {
        return -2;
    }
    return 0;
}

static_assert(MONAD_UINT256_SIZE == sizeof(::intx::uint256));
