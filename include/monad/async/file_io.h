#pragma once

#include "task.h"

#include <liburing.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief An offset into a file
typedef uint64_t monad_async_file_offset;

//! \brief The public attributes of an open file
typedef struct monad_async_file_head
{
    // The following are not user modifiable
    monad_async_executor executor;
} *monad_async_file;

/*! \brief EXPENSIVE Suspend execution of the task until the file has been
opened. See `man open2` to explain parameters.

This is a relatively expensive operation as it may do up to two mallocs and
several syscalls per call.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_file_create(
    monad_async_file *file, monad_async_task task, monad_async_file base,
    char const *subpath, struct open_how *how);

//! \brief Suspend execution of the task until the file has been closed
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_file_destroy(monad_async_task task, monad_async_file file);

//! \brief Suspend execution of the task until the file's valid extents have
//! been modified as per the `fallocate` call, see `man fallocate` for more.
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_file_fallocate(
    monad_async_task task, monad_async_file file, int mode,
    monad_async_file_offset offset, monad_async_file_offset len);

/*! \brief Initiate a read from an open file using `iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man readv2` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of iovecs have lifetime until
the read completes. The only exception here is if `nr_vecs` is one.
*/
extern void monad_async_task_file_read(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, int buffer_index, const struct iovec *iovecs,
    unsigned nr_vecs, monad_async_file_offset offset, int flags);

/*! \brief Initiate a write to an open file using `iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man writev2` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of iovecs have lifetime until
the writes completes. The only exception here is if `nr_vecs` is one.
*/
extern void monad_async_task_file_write(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, int buffer_index, const struct iovec *iovecs,
    unsigned nr_vecs, monad_async_file_offset offset, int flags);

//! \brief Initiate a flush of dirty file extents using `iostatus` as the
//! identifier. Returns immediately unless there are no free io_uring submission
//! entries. See `man sync_file_range` to explain parameters. The i/o priority
//! used will be that from the task's current i/o priority setting. This is the
//! right call to use to encourage the kernel to flush a region of data now, it
//! is the wrong call to ensure write durability as it neither flushes metadata
//! nor tells the storage device to flush.
extern void monad_async_task_file_range_sync(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, unsigned bytes, monad_async_file_offset offset,
    int flags);

//! \brief EXPENSIVE Initiate a durable sync of an open file using `iostatus` as
//! the identifier. Returns immediately unless there are no free io_uring
//! submission entries. The i/o priority used will be that from the task's
//! current i/o priority setting. This is the right call to use to ensure
//! written data is durably placed onto non-volatile storage.
extern void monad_async_task_file_durable_sync(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file);

#ifdef __cplusplus
}
#endif
