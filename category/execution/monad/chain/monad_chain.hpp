#pragma once

#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/monad/chain/monad_revision.h>
#include <category/core/config.hpp>
#include <category/core/bytes.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Transaction;
class FeeBuffer;

struct MonadChainContext
{
    FeeBuffer const &fee_buffer;
};

struct MonadChain : Chain
{
    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const override;

    virtual monad_revision
    get_monad_revision(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual size_t
    get_max_code_size(uint64_t block_number, uint64_t timestamp) const override;

    virtual uint256_t get_balance(
        uint64_t block_number, uint64_t timestamp, uint64_t i, Address const &,
        State &, void *chain_context) const override;

    virtual Result<void> validate_transaction(
        uint64_t block_number, uint64_t timestamp, uint64_t i,
        Transaction const &, Address const &sender, State &,
        void *chain_context) const override;
};

uint256_t get_max_reserve(monad_revision, Address const &, State &);

MONAD_NAMESPACE_END
