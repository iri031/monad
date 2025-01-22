#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/emitter/wal_emitter.hpp>

#include <evmc/hex.hpp>

#include <sstream>

using std::ios;

MONAD_NAMESPACE_BEGIN

namespace
{

    constexpr auto WAL_ENTRY_SIZE =
        static_cast<std::streamoff>(sizeof(monad_wal_action));

    byte_string slurp_file(std::filesystem::path const &path)
    {
        MONAD_ASSERT(
            std::filesystem::exists(path) &&
            std::filesystem::is_regular_file(path));
        std::ifstream is(path);
        MONAD_ASSERT(is);
        return {
            std::istreambuf_iterator<char>(is),
            std::istreambuf_iterator<char>()};
    }
}

WalEmitter::WalEmitter(std::filesystem::path const &ledger_dir)
    : ledger_dir_{ledger_dir}
{
    cursor_.open(ledger_dir_ / "wal", std::ios::binary);
    MONAD_ASSERT(cursor_);
}

std::optional<BlockEmitter::EmitterResult> WalEmitter::next()
{
    monad_wal_action action;
    auto const pos = cursor_.tellg();
    if (MONAD_LIKELY(cursor_.read(
            reinterpret_cast<char *>(&action), sizeof(monad_wal_action)))) {
        auto const header_filename =
            evmc::hex(byte_string_view{std::bit_cast<bytes32_t>(action.id)}) +
            ".header";
        auto const header_data = slurp_file(ledger_dir_ / header_filename);
        byte_string_view header_view{header_data};
        auto const header_res = rlp::decode_consensus_block_header(header_view);
        MONAD_ASSERT_PRINTF(
            !header_res.has_error(),
            "Could not rlp decode file %s",
            header_filename.c_str());

        auto const body_filename =
            evmc::hex(header_res.value().block_body_id) + ".body";
        auto const body_data = slurp_file(ledger_dir_ / body_filename);
        auto const checksum = to_bytes(blake3(body_data));
        MONAD_ASSERT_PRINTF(
            checksum == header_res.value().block_body_id,
            "Checksum failed for bft block body %s",
            body_filename.c_str());
        byte_string_view body_view{body_data};
        auto const body_res = rlp::decode_consensus_block_body(body_view);
        MONAD_ASSERT_PRINTF(
            !header_res.has_error(),
            "Could not rlp decode file %s",
            body_filename.c_str());

        return EmitterResult{
            .action = action.action,
            .block =
                Block{
                    .header = header_res.value().execution_inputs,
                    .transactions = std::move(body_res.value().transactions),
                    .ommers = std::move(body_res.value().ommers),
                    .withdrawals = std::move(body_res.value().withdrawals)},
            .header = std::move(header_res.value())};
    }
    else {
        // execution got ahead
        cursor_.clear();
        cursor_.seekg(pos);
        return {};
    }
}

bool WalEmitter::rewind_to(monad_wal_action const &rewind_action)
{
    cursor_.seekg(0, ios::end);
    auto const size_on_start = cursor_.tellg();
    cursor_.seekg(0, ios::beg);

    if (size_on_start >= WAL_ENTRY_SIZE) {
        auto const pos =
            (size_on_start / WAL_ENTRY_SIZE) * WAL_ENTRY_SIZE - WAL_ENTRY_SIZE;
        cursor_.seekg(pos);
        while (cursor_) {
            monad_wal_action action;
            if (!cursor_.read(
                    reinterpret_cast<char *>(&action),
                    sizeof(monad_wal_action))) {
                MONAD_ASSERT(false);
            }

            if (std::bit_cast<bytes32_t>(action.id) ==
                    std::bit_cast<bytes32_t>(rewind_action.id) &&
                action.action == rewind_action.action) {
                cursor_.seekg(-WAL_ENTRY_SIZE, ios::cur);

                return true;
            }

            cursor_.seekg(-2 * WAL_ENTRY_SIZE, ios::cur);
        }
    }
    cursor_.clear();
    cursor_.seekg(0, ios::beg);

    return false;
}

MONAD_NAMESPACE_END
