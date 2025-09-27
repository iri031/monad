// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/statesync/statesync_messages.h>

#include <quill/Quill.h>

#include <cerrno>
#include <chrono>
#include <cstring>
#include <sys/socket.h>
#include <sys/un.h>
#include <thread>
#include <unistd.h>
#include <utility>

struct monad_statesync_server_network
{
    int fd;
    monad::byte_string obuf;
    std::string path;

    [[nodiscard]] bool connect()
    {
        fd = socket(AF_UNIX, SOCK_STREAM, 0);
        MONAD_ASSERT_PRINTF(
            fd >= 0, "failed to create socket: %s", std::strerror(errno));
        struct sockaddr_un addr;
        memset(&addr, 0, sizeof(addr));
        addr.sun_family = AF_UNIX;
        strncpy(addr.sun_path, path.c_str(), sizeof(addr.sun_path) - 1);
        if (::connect(fd, (sockaddr *)&addr, sizeof(addr)) != 0) {
            LOG_WARNING(
                "connection to {} failed: {}", path, std::strerror(errno));
            return false;
        }
        return true;
    }

    monad_statesync_server_network(char const *const path)
        : path{path}
    {
        (void)connect();
    }

    ~monad_statesync_server_network()
    {
        if (fd >= 0) {
            (void)close(fd);
        }
    }
};

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr size_t SEND_BATCH_SIZE = 64 * 1024;

    void send(int const fd, byte_string_view const buf)
    {
        size_t nsent = 0;
        while (nsent < buf.size()) {
            ssize_t const res =
                ::send(fd, buf.data() + nsent, buf.size() - nsent, 0);
            if (res == -1) {
                if (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) {
                    LOG_ERROR(
                        "send error: {}, fd={}, nsent={}, size={}",
                        std::strerror(errno),
                        fd,
                        nsent,
                        buf.size());
                    break;
                }
                else {
                    continue;
                }
            }
            nsent += static_cast<size_t>(res);
        }
    }
}

ssize_t statesync_server_recv(
    monad_statesync_server_network *const net, unsigned char *buf, size_t n)
{
    while (true) {
        ssize_t const ret = recv(net->fd, buf, n, MSG_DONTWAIT);
        if (ret == 0 || (ret < 0 && (errno == ECONNRESET || errno == ENOTCONN ||
                                     errno == EBADF))) {
            LOG_WARNING("connection closed, reconnecting");
            (void)close(net->fd);
            net->fd = -1;
            if (!net->connect()) {
                return -ENOTCONN;
            }
        }
        else if (
            ret < 0 &&
            (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR)) {
            LOG_ERROR("recv error: {}", std::strerror(errno));
            (void)close(net->fd);
            net->fd = -1;
            return -ENOTCONN;
        }
        else {
            return ret;
        }
    }
}

void statesync_server_send_upsert(
    monad_statesync_server_network *const net, monad_sync_type const type,
    unsigned char const *const v1, uint64_t const size1,
    unsigned char const *const v2, uint64_t const size2)
{
    MONAD_ASSERT(v1 != nullptr || size1 == 0);
    MONAD_ASSERT(v2 != nullptr || size2 == 0);
    MONAD_ASSERT(
        type == SYNC_TYPE_UPSERT_CODE || type == SYNC_TYPE_UPSERT_ACCOUNT ||
        type == SYNC_TYPE_UPSERT_STORAGE ||
        type == SYNC_TYPE_UPSERT_ACCOUNT_DELETE ||
        type == SYNC_TYPE_UPSERT_STORAGE_DELETE ||
        type == SYNC_TYPE_UPSERT_HEADER);

    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(type);
    uint64_t const size = size1 + size2;
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&size), sizeof(size));
    if (v1 != nullptr) {
        net->obuf.append(v1, size1);
    }
    if (v2 != nullptr) {
        net->obuf.append(v2, size2);
    }

    if (net->obuf.size() >= SEND_BATCH_SIZE) {
        send(net->fd, net->obuf);
        net->obuf.clear();
    }

    LOG_DEBUG(
        "sending upsert type={} {} ns={}",
        std::to_underlying(type),
        fmt::format(
            "v1=0x{:02x} v2=0x{:02x}",
            fmt::join(std::as_bytes(std::span(v1, size1)), ""),
            fmt::join(std::as_bytes(std::span(v2, size2)), "")),
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - start));
}

void statesync_server_send_done(
    monad_statesync_server_network *const net, monad_sync_done const msg)
{
    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    net->obuf.push_back(SYNC_TYPE_DONE);
    net->obuf.append(
        reinterpret_cast<unsigned char const *>(&msg), sizeof(msg));
    send(net->fd, net->obuf);
    net->obuf.clear();
    LOG_DEBUG(
        "sending done success={} prefix={} n={} time={}",
        msg.success,
        msg.prefix,
        msg.n,
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - start));
}

MONAD_NAMESPACE_END
