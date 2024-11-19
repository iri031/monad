#include <monad/chain/monad_chain.hpp>
#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/execution/validate_block.hpp>

#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

Result<void> MonadChain::on_pre_commit_outputs(
    std::vector<Receipt> const &receipts,
    std::vector<BlockHeader> const &ommers, bytes32_t const &parent_hash,
    BlockHeader &hdr) const
{
    uint64_t const gas_used = receipts.empty() ? 0 : receipts.back().gas_used;

    // YP eq. 56
    if (MONAD_UNLIKELY(gas_used > hdr.gas_limit)) {
        LOG_ERROR(
            "Block: {}, Computed gas used {} greater than limit {}",
            hdr.number,
            gas_used,
            hdr.gas_limit);
        return BlockError::GasAboveLimit;
    }

    hdr.parent_hash = parent_hash;
    hdr.gas_used = gas_used;
    hdr.ommers_hash = compute_ommers_hash(ommers);
    hdr.logs_bloom = compute_bloom(receipts);

    return success();
}

bool MonadChain::on_post_commit_outputs(
    evmc_revision const, bytes32_t const &state_root,
    bytes32_t const &receipts_root, bytes32_t const &transactions_root,
    std::optional<bytes32_t> const &withdrawals_root, BlockHeader &hdr) const
{
    hdr.state_root = state_root;
    hdr.receipts_root = receipts_root;
    hdr.transactions_root = transactions_root;
    hdr.withdrawals_root = withdrawals_root;

    return true;
}

MONAD_NAMESPACE_END
