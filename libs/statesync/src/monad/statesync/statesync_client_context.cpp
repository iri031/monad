#include <monad/core/block.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_version.h>

#include <sys/sysinfo.h>

using namespace monad;

monad_statesync_client_context::monad_statesync_client_context(
    std::vector<std::filesystem::path> const dbname_paths,
    std::filesystem::path const genesis, monad_statesync_client *const sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request))
    : db{machine,
         mpt::OnDiskDbConfig{
             .append = true,
             .compaction = false,
             .rd_buffers = 8192,
             .wr_buffers = 32,
             .uring_entries = 128,
             .sq_thread_cpu = get_nprocs() - 1,
             .dbname_paths = dbname_paths}}
    , tdb{db}
    , progress(
          MONAD_STATESYNC_N_PREFIXES,
          {db.get_latest_block_id(), db.get_latest_block_id()})
    , version(MONAD_STATESYNC_N_PREFIXES, MONAD_STATESYNC_VERSION + 1)
    , target{db.get_latest_block_id()}
    , current{db.get_latest_block_id() == mpt::INVALID_BLOCK_ID ? 0 : db.get_latest_block_id() + 1}
    , expected_root{NULL_ROOT}
    , n_upserts{0}
    , genesis{genesis}
    , sync{sync}
    , statesync_send_request{statesync_send_request}
{
}
