#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>
#include <brotli/types.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

#include <iostream>

MONAD_NAMESPACE_BEGIN

BlockDb::BlockDb(std::filesystem::path const &dir)
    : db_{dir.c_str()}
{
}

bool BlockDb::get(uint64_t const num, Block &block) const
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
    // TODO: Blocks from archiver isn't compressed
    auto view = to_byte_string_view(result.value());
    // size_t brotli_size = std::max(result->size() * 100, 1ul << 20); // TODO
    // byte_string brotli_buffer;
    // brotli_buffer.resize(brotli_size);
    // auto const brotli_result = BrotliDecoderDecompress(
    //     view.size(), view.data(), &brotli_size, brotli_buffer.data());
    // brotli_buffer.resize(brotli_size);
    // MONAD_ASSERT(brotli_result == BROTLI_DECODER_RESULT_SUCCESS);
    // byte_string_view view2{brotli_buffer};

    auto const decoded_block = rlp::decode_block_with_tx_sender(view);
    if (decoded_block.has_error()) {
        std::cerr << decoded_block.assume_error().message().c_str()
                  << std::endl;
    }
    MONAD_ASSERT(!decoded_block.has_error());
    MONAD_ASSERT(view.size() == 0);
    block = decoded_block.value();
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
