#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

constexpr unsigned MONAD_UINT256_SIZE = 32;

// 0 on success
// -1 on invalid arg
// -2 on out of range
int monad_uint256_from_string(
    char const *from, unsigned char (*to)[MONAD_UINT256_SIZE]);

#ifdef __cplusplus
}
#endif
