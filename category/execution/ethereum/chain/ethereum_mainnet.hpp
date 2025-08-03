#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Receipt;
struct Transaction;

inline constexpr size_t MAX_CODE_SIZE_EIP170 = 24 * 1024; // 0x6000

struct EthereumMainnet : Chain
{
    virtual uint256_t get_chain_id() const override;

    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void>
    static_validate_header(BlockHeader const &) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const override;

    virtual size_t
    get_max_code_size(uint64_t block_number, uint64_t timestamp) const override;

    virtual GenesisState get_genesis_state() const override;

    virtual uint256_t get_balance(
        uint64_t block_number, uint64_t timestamp, uint64_t i, Address const &,
        State &, void *chain_context) const override;

    virtual Result<void> validate_transaction(
        uint64_t block_number, uint64_t timestamp, uint64_t i,
        Transaction const &, Address const &sender, State &,
        void *chain_context) const override;
};

MONAD_NAMESPACE_END
