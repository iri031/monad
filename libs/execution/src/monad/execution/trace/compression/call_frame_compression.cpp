#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/execution/trace/compression/call_frame_compression.hpp>
#include <monad/execution/trace/rlp/call_frame_rlp.hpp>
#include <monad/rlp/config.hpp>

#include <lz4.h>

#include <span>
#include <vector>

#include <fstream>
#include <iostream>

MONAD_NAMESPACE_BEGIN

byte_string compress_call_frames(byte_string_view const rlp_call_frames)
{
    int const size_required =
        LZ4_compressBound(static_cast<int>(rlp_call_frames.size()));
    MONAD_ASSERT(size_required);
    size_t const size_required_t = static_cast<size_t>(size_required);

    thread_local std::unique_ptr<char[]> buffer;
    thread_local size_t buffer_capacity = 0;

    if (MONAD_UNLIKELY(buffer_capacity < size_required_t)) {
        buffer.reset(new char[size_required_t]);
        buffer_capacity = size_required_t;
    }

    int const compressed_size = LZ4_compress_default(
        reinterpret_cast<char const *>(rlp_call_frames.data()),
        buffer.get(),
        static_cast<int>(rlp_call_frames.size()),
        static_cast<int>(size_required));

    MONAD_ASSERT(compressed_size > 0);

    static std::ofstream ofile("call_trace_size.csv");
    ofile << rlp_call_frames.length() << "," << compressed_size << std::endl;

    return byte_string(
        reinterpret_cast<uint8_t const *>(buffer.get()),
        reinterpret_cast<uint8_t const *>(buffer.get() + compressed_size));
}

byte_string
decompress_call_frames(byte_string_view const compressed_call_frames)
{
    static constexpr size_t max_compression_factor = 10000;
    size_t max_decompressed_size =
        compressed_call_frames.size() * max_compression_factor;

    byte_string buffer;
    buffer.resize(max_decompressed_size);

    // Decompress (LZ4_decompress_safe returns the number of bytes decompressed
    // or a negative error code).
    int const decompressed_size = LZ4_decompress_safe(
        reinterpret_cast<char const *>(compressed_call_frames.data()),
        reinterpret_cast<char *>(buffer.data()),
        static_cast<int>(compressed_call_frames.size()),
        static_cast<int>(buffer.size()));

    MONAD_ASSERT(decompressed_size >= 0);

    size_t const decompressed_size_t = static_cast<size_t>(decompressed_size);

    buffer.resize(decompressed_size_t);

    return buffer;
}

MONAD_NAMESPACE_END
