#pragma once

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct MonadChain : Chain
{
    virtual Result<void> on_pre_commit_outputs(
        std::vector<Receipt> const &, std::vector<BlockHeader> const &,
        BlockHeader &) const override;

    virtual bool on_post_commit_outputs(
        evmc_revision, bytes32_t const &state_root,
        bytes32_t const &receipts_root, bytes32_t const &transactions_root,
        std::optional<bytes32_t> const &withdrawals_root,
        BlockHeader &) const override;
};

MONAD_NAMESPACE_END
