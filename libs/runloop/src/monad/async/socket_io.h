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
    // Either the locally bound or peer of connected socket
    struct sockaddr addr;
    socklen_t addr_len;

    // The following are not user modifiable
    monad_async_executor executor;
} *monad_async_socket;

/*! \brief EXPENSIVE Create a socket. See `man socket` to explain parameters.

At least one malloc is performed, and possibly more.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_create(
    monad_async_socket *sock, monad_async_task task, int domain, int type,
    int protocol, unsigned flags);

//! \brief Suspend execution of the task until the socket has been closed
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_socket_destroy(monad_async_task task, monad_async_socket sock);

/*! \brief EXPENSIVE Bind a socket to an interface and port.

This is done by blocking syscall, as io_uring is currently incapable of doing
listening socket setup by itself.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_bind(
    monad_async_socket sock, const struct sockaddr *addr, socklen_t addrlen);

/*! \brief EXPENSIVE Make a bound socket available for incoming connections.

This is done by blocking syscall, as io_uring is currently incapable of doing
listening socket setup by itself.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_socket_listen(monad_async_socket sock, int backlog);

/*! \brief CANCELLATION POINT Transfers the socket to io_uring, which may
require suspending the task.

As io_uring is currently incapable of doing listening socket setup by itself,
there is an explicit step for transferring the configured socket to io_uring
as it is an expensive operation.

Newer Linux kernels have an io_uring capable of connecting socket setup and
creation entirely within io_uring. If your kernel is so capable, that is used,
else blocking syscalls are used and the socket transferred into io_uring.

When this call returns, all syscall-created resources are released and io_uring
exclusively manages the socket.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_socket_transfer_to_uring(
    monad_async_task task, monad_async_socket sock);

/*! \brief CANCELLATION POINT Suspend execution of the task if there is no
pending connection on the socket until there is a new connection. See `man
accept4` to explain parameters.

Note that if `SOCK_CLOEXEC` is set in the flags, io_uring will fail the request
(this is non-obvious, cost me half a day of debugging, so I document it here)
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_accept(
    monad_async_socket *connected_sock, monad_async_task task,
    monad_async_socket listening_sock, int flags);

/*! \brief Initiate the connection of an open socket using `iostatus` as the
identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man connect` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.
*/
extern void monad_async_task_socket_connect(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, const struct sockaddr *addr, socklen_t addrlen);

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
    monad_async_socket sock, int buffer_index, struct msghdr *msg,
    unsigned flags);

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
    unsigned flags);

#ifdef __cplusplus
}
#endif
