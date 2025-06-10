#pragma once

#include <monad/chain/chain.hpp>
#include <monad/chain/monad_revision.h>
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

class InflightExpensesBuffer;
struct Block;
struct BlockHeader;
struct Db;
struct Transaction;

struct MonadChain : Chain
{
    using Chain::Chain;

    virtual evmc_revision get_revision() const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual uint64_t compute_gas_refund(
        Transaction const &, uint64_t gas_remaining,
        uint64_t refund) const override;

    virtual monad_revision get_monad_revision() const = 0;

    virtual size_t get_max_code_size() const override;
};

uint512_t get_inflight_expense(monad_revision, Transaction const &);

uint256_t get_max_reserve_balance(monad_revision, Address const &sender, Db &);

Result<void> validate_block(
    Block const &, std::vector<Address> const &senders,
    std::vector<uint256_t> const &max_reserve_balances,
    InflightExpensesBuffer const &);

MONAD_NAMESPACE_END
