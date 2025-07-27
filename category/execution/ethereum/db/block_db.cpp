#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/block_db.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>
#include <brotli/types.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <optional>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

BlockDb::BlockDb(std::filesystem::path const &dir)
    : db_{dir.c_str()}
{
}

bool BlockDb::get(
    monad_chain_config const chain_config, uint64_t const num,
    Block &block) const
{
    auto const key = std::to_string(num);
    auto result = db_.get(key.c_str());
    if (!result.has_value()) {
        auto const folder = std::to_string(num / 1000000) + 'M';
        auto const key = folder + '/' + std::to_string(num);
        result = db_.get(key.c_str());
    }
    if (!result.has_value()) {
        return false;
    }

    if (chain_config == CHAIN_CONFIG_ETHEREUM_MAINNET) {
        auto const view = to_byte_string_view(result.value());
        size_t brotli_size = std::max(result->size() * 100, 1ul << 20); // TODO
        byte_string brotli_buffer;
        brotli_buffer.resize(brotli_size);
        auto const brotli_result = BrotliDecoderDecompress(
            view.size(), view.data(), &brotli_size, brotli_buffer.data());
        brotli_buffer.resize(brotli_size);
        MONAD_ASSERT(brotli_result == BROTLI_DECODER_RESULT_SUCCESS);
        byte_string_view view2{brotli_buffer};
        auto const decoded_block = rlp::decode_block(view2);
        MONAD_ASSERT(!decoded_block.has_error());
        MONAD_ASSERT(view2.empty());

        block = decoded_block.value();
    }
    else {
        // blocks in monad archiver aren't compressed, but have with sender
        // info
        auto view = to_byte_string_view(result.value());
        auto const decoded_block = rlp::decode_block_with_tx_sender(view);
        MONAD_ASSERT(!decoded_block.has_error());
        MONAD_ASSERT(view.empty());

        block = decoded_block.value();
    }

    // Only testnet's archive (initially) was bad
    if (chain_config == CHAIN_CONFIG_MONAD_TESTNET) {
        block.withdrawals = {std::make_optional(std::vector<Withdrawal>())};
    }
    return true;
}

void BlockDb::upsert(uint64_t const num, Block const &block) const
{
    auto const key = std::to_string(num);
    auto const encoded_block = rlp::encode_block(block);
    size_t brotli_size = BrotliEncoderMaxCompressedSize(encoded_block.size());
    MONAD_ASSERT(brotli_size);
    byte_string brotli_buffer;
    brotli_buffer.resize(brotli_size);
    auto const brotli_result = BrotliEncoderCompress(
        BROTLI_DEFAULT_QUALITY,
        BROTLI_DEFAULT_WINDOW,
        BROTLI_MODE_GENERIC,
        encoded_block.size(),
        encoded_block.data(),
        &brotli_size,
        brotli_buffer.data());
    MONAD_ASSERT(brotli_result == BROTLI_TRUE);
    brotli_buffer.resize(brotli_size);
    std::string_view const value{
        reinterpret_cast<char const *>(brotli_buffer.data()),
        brotli_buffer.size()};
    db_.upsert(key.c_str(), value);
}

bool BlockDb::remove(uint64_t const num) const
{
    auto const key = std::to_string(num);
    return db_.remove(key.c_str());
}

MONAD_NAMESPACE_END
