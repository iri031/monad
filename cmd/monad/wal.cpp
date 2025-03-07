#include "wal.hpp"
#include "file_io.hpp"

#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>

#include <evmc/hex.hpp>

#include <sstream>

using std::ios;

MONAD_NAMESPACE_BEGIN

WalReader::WalReader(
    MonadChain const &chain, std::filesystem::path const &ledger_dir)
    : chain_{chain}
    , ledger_dir_{ledger_dir}
    , header_dir_{ledger_dir / "headers"}
    , bodies_dir_{ledger_dir / "bodies"}
{
    cursor_.open(ledger_dir_ / "wal", std::ios::binary);
    MONAD_ASSERT(cursor_);
}

std::optional<WalReader::Result> WalReader::next()
{
    WalEntry entry;
    auto const pos = cursor_.tellg();
    MONAD_ASSERT(pos != -1);
    if (MONAD_LIKELY(
            cursor_.read(reinterpret_cast<char *>(&entry), sizeof(WalEntry)))) {
        MonadConsensusBlockHeader const header =
            read_header(chain_, entry.id, header_dir_);
        bytes32_t bft_body_id = header.block_body_id;

        return Result{
            .action = entry.action,
            .block_id = entry.id,
            .header = std::move(header),
            .body = read_body(bft_body_id, bodies_dir_)};
    }
    else {
        // execution got ahead
        cursor_.clear();
        cursor_.seekg(pos);
        return {};
    }
}

WalWriter::WalWriter(std::filesystem::path const &ledger_dir)
    : wal_path_{ledger_dir / "wal"}
    , cursor_(wal_path_, std::ios::binary | std::ios::trunc)
{
    MONAD_ASSERT(cursor_);
}

void WalWriter::write(WalAction action, MonadConsensusBlockHeader const &header)
{
    WalEntry entry{
        .action = action,
        .id = to_bytes(blake3(rlp::encode_consensus_block_header(header)))};
    cursor_.write(reinterpret_cast<char *>(&entry), sizeof(WalEntry));
    cursor_.flush();
    MONAD_ASSERT(cursor_);
}

MONAD_NAMESPACE_END
