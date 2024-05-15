#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>

#include <quill/Quill.h>

#include <sys/socket.h>
#include <sys/un.h>

using namespace monad;

struct monad_statesync_client
{
    std::deque<monad_sync_request> requests;
};

void statesync_send_request(
    struct monad_statesync_client *const sync,
    struct monad_sync_request const rq)
{
    sync->requests.emplace_back(rq);
}

MONAD_NAMESPACE_BEGIN

quill::Logger *tracer = nullptr;

MONAD_NAMESPACE_END

int accept(char const *const path)
{
    int const fd = socket(AF_UNIX, SOCK_STREAM, 0);
    MONAD_ASSERT(fd != -1);

    sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, path, sizeof(addr.sun_path) - 1);
    MONAD_ASSERT(bind(fd, (sockaddr *)&addr, sizeof(addr)) == 0);
    MONAD_ASSERT(listen(fd, 1) == 0);

    sockaddr_un peer_addr;
    socklen_t peer_addr_size = sizeof(peer_addr);
    int const peerfd = accept(fd, (sockaddr *)&peer_addr, &peer_addr_size);
    MONAD_ASSERT(peerfd != -1);
    LOG_INFO("accepted connection on path {}", path);
    return peerfd;
}

void read_n(int const fd, byte_string &buf, size_t n)
{
    buf.resize(n);
    auto *ptr = buf.data();
    while (n != 0) {
        auto const res = recv(fd, ptr, n, 0);
        if (res == -1) {
            continue;
        }
        ptr += res;
        n -= static_cast<size_t>(res);
    }
}

void send_n(int const fd, void const *const buf, size_t const len)
{
    size_t nsent = 0;
    while (nsent < len) {
        ssize_t const res =
            send(fd, static_cast<char const *>(buf) + nsent, len - nsent, 0);
        if (res == -1) {
            continue;
        }
        nsent += static_cast<size_t>(res);
    }
}

int main(int const, char const *const[])
{
    quill::start(true);

    auto const livefd = accept("/tmp/monadlive");

    // size_t ndone = 0;
    uint64_t target = 3000000;

    char const *const dbname_path = "test.db";

    monad_statesync_client sync;
    auto *const ctx = monad_statesync_client_context_create(
        &dbname_path, 1, "", &sync, &statesync_send_request);

    auto const send_request = [&] {
        constexpr monad_sync_type type = SyncTypeRequest;
        send_n(livefd, &type, 1);
        send_n(livefd, &sync.requests.front(), sizeof(monad_sync_request));
    };

    auto const state_root =
        0x8e7ab0771fa333e1369fd48374010b8a21283a70690c6064fe2ecf091a1719ec_bytes32;
    monad_sync_target msg;
    msg.n = target;
    std::memcpy(msg.state_root, state_root.bytes, sizeof(state_root));
    monad_statesync_client_handle_target(ctx, msg);
    if (!sync.requests.empty()) {
        send_request();
    }

    byte_string buf;
    while (!monad_statesync_client_has_reached_target(ctx)) {
        monad_sync_type type;
        auto size = recv(livefd, &type, 1, MSG_DONTWAIT);
        if (size == 1) {
            buf.push_back(type);
            if (buf.back() == SyncTypeUpsertHeader) {
                read_n(livefd, buf, sizeof(monad_sync_upsert_header));
                auto const hdr =
                    *reinterpret_cast<monad_sync_upsert_header const *>(
                        buf.data());
                read_n(livefd, buf, hdr.key_size + hdr.value_size);
                monad_statesync_client_handle_upsert(
                    ctx,
                    buf.data(),
                    hdr.key_size,
                    buf.data() + hdr.key_size,
                    hdr.value_size,
                    hdr.code);
            }
            else if (buf.back() == SyncTypeDone) {
                read_n(livefd, buf, sizeof(monad_sync_done));
                monad_statesync_client_handle_done(
                    ctx,
                    *reinterpret_cast<monad_sync_done const *>(buf.data()));
                sync.requests.pop_front();
                //++ndone;
                // if (ndone == 256 && target != 12'270'000) {
                //    target = 12'270'000;
                //    send_target();
                //    ndone = 0;
                //}
                while (!sync.requests.empty() &&
                       sync.requests.front().target != target) {
                    sync.requests.pop_front();
                }
                if (!sync.requests.empty()) {
                    send_request();
                }
                buf.clear();
            }
            else {
                MONAD_ASSERT(false);
            }
        }
    }

    MONAD_ASSERT(monad_statesync_client_finalize(ctx));

    TrieDb db{ctx->db};
    LOG_INFO("finished with db_root {}", db.state_root());

    MONAD_ASSERT(sync.requests.empty());
    MONAD_ASSERT(unlink("/tmp/monadlive") == 0);
    monad_statesync_client_context_destroy(ctx);
}
