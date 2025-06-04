#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/monad/core/monad_block.hpp>

#include <ankerl/unordered_dense.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <immer/array.hpp>
#pragma GCC diagnostic pop

#include <functional>
#include <vector>

MONAD_NAMESPACE_BEGIN

constexpr unsigned EXECUTION_DELAY = 3;

struct FeeBufferResult
{
    uint512_t cumulative_fee{0};
    uint512_t tx_fee{0};
    unsigned num_fees{0};

    constexpr bool operator==(FeeBufferResult const &) const = default;
};

class FeeBuffer
{
    using Fees = ankerl::unordered_dense::segmented_map<
        Address, std::vector<std::pair<uint64_t, uint512_t>>>;
    using ProposalFees = immer::array<Fees>;

    ankerl::unordered_dense::segmented_map<
        bytes32_t, std::pair<uint64_t, ProposalFees>>
        proposals_{};
    uint64_t block_number_{0};
    bytes32_t id_{NULL_HASH_BLAKE3};
    bytes32_t parent_id_{NULL_HASH_BLAKE3};
    Fees fees_{};

public:
    void
    set(uint64_t block_number, bytes32_t const &id, bytes32_t const &parent_id);
    void note(uint64_t i, Address const &, uint512_t fee);
    void propose();
    void finalize(bytes32_t const &id);
    FeeBufferResult get(uint64_t i, Address const &) const;
};

static_assert(sizeof(FeeBuffer) == 200);
static_assert(alignof(FeeBuffer) == 8);

FeeBuffer make_fee_buffer(
    uint64_t block_to_execute,
    std::function<std::tuple<
        bytes32_t, MonadConsensusBlockHeaderV1, std::vector<Transaction>>(
        uint64_t block)> const &read_header_and_transactions);

MONAD_NAMESPACE_END
