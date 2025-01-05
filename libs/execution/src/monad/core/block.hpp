#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHeader
{
    Receipt::Bloom logs_bloom{};
    bytes32_t parent_hash{};
    bytes32_t ommers_hash{};
    bytes32_t state_root{};
    bytes32_t transactions_root{};
    bytes32_t receipts_root{};
    bytes32_t prev_randao{}; // aka mix_hash
    uint256_t difficulty{};

    uint64_t number{0};
    uint64_t gas_limit{0};
    uint64_t gas_used{0};
    uint64_t timestamp{0};

    byte_string_fixed<8> nonce{};
    byte_string extra_data{};

    Address beneficiary{};

    std::optional<uint256_t> base_fee_per_gas{std::nullopt}; // EIP-1559
    std::optional<bytes32_t> withdrawals_root{std::nullopt}; // EIP-4895
    std::optional<uint64_t> blob_gas_used{std::nullopt}; // EIP-4844
    std::optional<uint64_t> excess_blob_gas{std::nullopt}; // EIP-4844
    std::optional<bytes32_t> parent_beacon_block_root{std::nullopt}; // EIP-4788

    // monad specific fields
    bytes32_t bft_block_id{};
    uint64_t round{};
    uint64_t parent_round{};

    friend bool operator==(BlockHeader const &, BlockHeader const &) = default;
};

struct Block
{
    BlockHeader header;
    std::vector<Transaction> transactions{};
    std::vector<BlockHeader> ommers{};
    std::optional<std::vector<Withdrawal>> withdrawals{std::nullopt};

    friend bool operator==(Block const &, Block const &) = default;
};

static_assert(sizeof(BlockHeader) == 776);
static_assert(alignof(BlockHeader) == 8);

static_assert(sizeof(Block) == 856);
static_assert(alignof(Block) == 8);

MONAD_NAMESPACE_END
