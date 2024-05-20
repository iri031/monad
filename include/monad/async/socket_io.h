#pragma once

#include "task.h"

#include <liburing.h>
#include <sys/socket.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief The public attributes of an open socket
typedef struct monad_async_socket_head
{
    // The following are not user modifiable
    monad_async_executor executor;
} *monad_async_socket;

/*! \brief EXPENSIVE, CANCELLATION POINT Suspend execution of the task until the
socket has been opened. See `man socket` to explain parameters.

This is a relatively expensive operation as it may do up to two mallocs and
several syscalls per call.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_create(
    monad_async_socket *sock, monad_async_task task, int domain, int type,
    int protocol, unsigned flags);

//! \brief Suspend execution of the task until the socket has been closed
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_socket_destroy(monad_async_task task, monad_async_socket file);

/*! \brief CANCELLATION POINT Suspend execution of the task if there is no
pending connection on the socket until there is a new connection. See `man
accept4` to explain parameters.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_accept(
    monad_async_task task, monad_async_socket sock, struct sockaddr *addr,
    socklen_t *addrlen, int flags);

/*! \brief Initiate a connect of an open socket using `iostatus` as the
identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man sendmsg` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of `addr` has lifetime until
the write completes.
*/
extern void monad_async_task_socket_connect(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, struct sockaddr *addr, socklen_t addrlen);

/*! \brief Initiate a shutdown of an open socket using `iostatus` as the
identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man shutdown` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.
*/
extern void monad_async_task_socket_shutdown(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, int how);

/*! \brief Initiate a read from an open socket using `iostatus` as the
identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man recvmsg` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of `msg` and everything it
points at have lifetime until the read completes.
*/
extern void monad_async_task_socket_recv(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, int buffer_index, struct msghdr *msg, int flags);

/*! \brief Initiate a write to an open socket using `iostatus` as the
identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man sendmsg` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of `msg` and everything it
points at have lifetime until the write completes.
*/
extern void monad_async_task_socket_send(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, int buffer_index, const struct msghdr *msg,
    int flags);

//! \brief Initiate a durable sync of an open file using `iostatus` as
//! the identifier. Returns immediately unless there are no free io_uring
//! submission entries. The i/o priority used will be that from the task's
//! current i/o priority setting. This is the right call to use to ensure
//! written data is durably placed onto non-volatile storage.
//!
//! Note that this operation generally takes milliseconds to complete.
extern void monad_async_task_file_durable_sync(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file);

#ifdef __cplusplus
}
#endif
