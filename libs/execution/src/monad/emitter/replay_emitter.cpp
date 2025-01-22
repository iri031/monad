#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/emitter/replay_emitter.hpp>

MONAD_NAMESPACE_BEGIN

ReplayEmitter::ReplayEmitter(
    std::filesystem::path const &block_db_path, uint64_t const start_block)
    : block_db_{block_db_path}
    , block_num_{start_block}
    , next_state_{MONAD_WAL_PROPOSE}
{
}

std::optional<BlockEmitter::EmitterResult> ReplayEmitter::next()
{
    auto const state = next_state_;
    Block eth_block;
    if (!block_db_.get(block_num_, eth_block)) {
        return std::nullopt;
    }
    switch (state) {
    case MONAD_WAL_PROPOSE:
        next_state_ = MONAD_WAL_FINALIZE;
        break;
    case MONAD_WAL_FINALIZE:
        next_state_ = MONAD_WAL_PROPOSE;
        ++block_num_;
        break;
    }
    return EmitterResult{
        .action = state,
        .block = eth_block,
        .header = MonadConsensusBlockHeader::from_eth_header(eth_block.header)};
}

MONAD_NAMESPACE_END
