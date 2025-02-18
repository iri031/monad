#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <immer/array.hpp>
#pragma GCC diagnostic pop

#include <cstdint>
#include <map>

MONAD_NAMESPACE_BEGIN

class BlockDb;

namespace mpt
{
    class Db;
}

class BlockHashBuffer
{
    static constexpr unsigned SIZE = 256;

    immer::array<bytes32_t> b_;
    uint64_t n_;

    BlockHashBuffer(immer::array<bytes32_t>, uint64_t);

public:
    BlockHashBuffer();

    uint64_t n() const;
    bytes32_t const &get(uint64_t) const;
    [[nodiscard]] BlockHashBuffer set(uint64_t, bytes32_t const &) const;
};

static_assert(sizeof(BlockHashBuffer) == 32);
static_assert(alignof(BlockHashBuffer) == 8);

struct BlockHashBufferChain
{
    BlockHashBuffer finalized_;
    std::map<uint64_t, BlockHashBuffer> proposed_;

public:
    explicit BlockHashBufferChain(BlockHashBuffer finalized);

    void propose(
        bytes32_t const &, uint64_t block_number, uint64_t round,
        uint64_t parent_round);
    void finalize(uint64_t round);
    BlockHashBuffer const &get(uint64_t round) const;
};

std::pair<BlockHashBuffer, bool>
make_block_hash_buffer_from_db(mpt::Db &, uint64_t block_number);

std::pair<BlockHashBuffer, bool>
make_block_hash_buffer_from_blockdb(BlockDb &, uint64_t block_number);

MONAD_NAMESPACE_END
