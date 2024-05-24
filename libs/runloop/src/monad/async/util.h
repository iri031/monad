#pragma once

#include "config.h"

#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Returns a temporary directory in which `O_DIRECT` files definitely
//! work
extern char const *monad_async_working_temporary_directory();

//! \brief Creates a temporary file, writing the path created into the buffer.
//! You will need to unlink this after yourself and close the file descriptor it
//! returns.
extern int monad_async_make_temporary_file(char *buffer, size_t buffer_len);

//! \brief Creates already deleted file so no need to clean it up
//! after. You will need to close the file descriptor it returns.
extern int monad_async_make_temporary_inode();

#ifdef __cplusplus
}
#endif
