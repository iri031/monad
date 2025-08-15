#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt2/traverse.hpp>
#include <category/statesync/statesync_server.h>
#include <category/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <chrono>
#include <fcntl.h>
#include <mutex>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <thread>
#include <unistd.h>

struct monad_statesync_server
{
    monad_statesync_server_context *context;
    monad_statesync_server_network *net;
    ssize_t (*statesync_server_recv)(
        monad_statesync_server_network *, unsigned char *, size_t);
    void (*statesync_server_send_upsert)(
        struct monad_statesync_server_network *, monad_sync_type,
        unsigned char const *v1, uint64_t size1, unsigned char const *v2,
        uint64_t size2);
    void (*statesync_server_send_done)(
        monad_statesync_server_network *, monad_sync_done);
};

using namespace monad;
using namespace monad::mpt2;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// byte_string from_prefix(uint64_t const prefix, size_t const n_bytes)
// {
//     byte_string bytes;
//     for (size_t i = 0; i < n_bytes; ++i) {
//         bytes.push_back((prefix >> ((n_bytes - i - 1) * 8)) & 0xff);
//     }
//     return bytes;
// }

bool statesync_server_handle_request(
    monad_statesync_server *const, monad_sync_request const)
{
    return true;
}

void monad_statesync_server_handle_request(
    monad_statesync_server *const sync, monad_sync_request const rq)
{
    auto const success = statesync_server_handle_request(sync, rq);
    if (!success) {
        LOG_INFO(
            "could not handle request prefix={} from={} until={} "
            "old_target={} target={}",
            rq.prefix,
            rq.from,
            rq.until,
            rq.old_target,
            rq.target);
    }
    sync->statesync_server_send_done(
        sync->net,
        monad_sync_done{
            .success = success, .prefix = rq.prefix, .n = rq.until});
}

MONAD_ANONYMOUS_NAMESPACE_END

struct monad_statesync_server *monad_statesync_server_create(
    monad_statesync_server_context *const ctx,
    monad_statesync_server_network *const net,
    ssize_t (*statesync_server_recv)(
        monad_statesync_server_network *, unsigned char *, size_t),
    void (*statesync_server_send_upsert)(
        monad_statesync_server_network *, monad_sync_type,
        unsigned char const *v1, uint64_t size1, unsigned char const *v2,
        uint64_t size2),
    void (*statesync_server_send_done)(
        monad_statesync_server_network *, struct monad_sync_done))
{
    return new monad_statesync_server(
        monad_statesync_server{
            .context = ctx,
            .net = net,
            .statesync_server_recv = statesync_server_recv,
            .statesync_server_send_upsert = statesync_server_send_upsert,
            .statesync_server_send_done = statesync_server_send_done});
}

void monad_statesync_server_run_once(struct monad_statesync_server *const sync)
{
    unsigned char buf[sizeof(monad_sync_request)];
    if (sync->statesync_server_recv(sync->net, buf, 1) != 1) {
        return;
    }
    MONAD_ASSERT(buf[0] == SYNC_TYPE_REQUEST);
    unsigned char *ptr = buf;
    uint64_t n = sizeof(monad_sync_request);
    while (n != 0) {
        auto const res = sync->statesync_server_recv(sync->net, ptr, n);
        if (res == -1) {
            continue;
        }
        ptr += res;
        n -= static_cast<size_t>(res);
    }
    auto const &rq = unaligned_load<monad_sync_request>(buf);
    monad_statesync_server_handle_request(sync, rq);
}

void monad_statesync_server_destroy(monad_statesync_server *const sync)
{
    delete sync;
}
