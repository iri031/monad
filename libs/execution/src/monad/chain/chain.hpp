#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct Block;
struct BlockHeader;
struct Receipt;

struct Chain
{
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision get_revision(BlockHeader const &) const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual Result<void> on_pre_commit_outputs(
        std::vector<Receipt> const &, std::vector<BlockHeader> const &,
        BlockHeader &) const = 0;

    virtual bool on_post_commit_outputs(
        evmc_revision, bytes32_t const &state_root,
        bytes32_t const &receipts_root, bytes32_t const &transactions_root,
        std::optional<bytes32_t> const &withdrawals_root,
        BlockHeader &) const = 0;
};

MONAD_NAMESPACE_END
