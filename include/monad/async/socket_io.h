#pragma once

#include "task.h"

#include <liburing.h>
#include <sys/socket.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief The status of an open socket
enum monad_async_socket_status : uint8_t
{
    monad_async_socket_status_not_created,
    monad_async_socket_status_bound,
    monad_async_socket_status_listening,
    monad_async_socket_status_connected,
    monad_async_socket_status_shutdown
};

//! \brief The public attributes of an open socket
typedef struct monad_async_socket_head
{
    // Either the locally bound or peer of connected socket
    struct sockaddr addr;
    socklen_t addr_len;

    // The following are not user modifiable
    enum monad_async_socket_status status;
    monad_async_executor executor;
} *monad_async_socket;

/*! \brief EXPENSIVE Create a socket. See `man socket` to explain parameters.
 */
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_create(
    monad_async_socket *sock, monad_async_task task, int domain, int type,
    int protocol, unsigned flags);

//! \brief Suspend execution of the task until the socket has been closed
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_socket_destroy(monad_async_task task, monad_async_socket file);

/*! \brief EXPENSIVE Bind a socket to an interface and port.

This is done by blocking syscall, as io_uring is currently incapable of doing
listening socket setup by itself.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_bind(
    monad_async_socket sock, const struct sockaddr *addr, socklen_t addrlen);

/*! \brief EXPENSIVE Make a bound socket available for incoming connections.

This is done by blocking syscall followed by transferring the socket into
io_uring, as io_uring is currently incapable of doing listening
socket setup by itself.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result
monad_async_task_socket_listen(monad_async_socket sock, int backlog);

/*! \brief CANCELLATION POINT Suspend execution of the task if there is no
pending connection on the socket until there is a new connection. See `man
accept4` to explain parameters.

Note that `SOCK_CLOEXEC` is XORed in the flags, so set that if you want to
disable it.
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_accept(
    monad_async_socket *connected_sock, monad_async_task task,
    monad_async_socket listening_sock, int flags);

/*! \brief CANCELLATION POINT Suspend execution of the task until the connection
either succeeds or fails.

Actual creation of the socket is delayed until this call as on newer Linux
kernels it is possible to have io_uring perform socket setup and creation
without needing to perform blocking syscalls (it cannot set up listening
sockets, so we need to defer the setup until you either connect or bind).
*/
MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_task_socket_connect(
    monad_async_task task, monad_async_socket sock, struct sockaddr *addr,
    socklen_t addrlen);

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

#ifdef __cplusplus
}
#endif
