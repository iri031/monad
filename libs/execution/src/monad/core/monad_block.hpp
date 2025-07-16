#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/variant.hpp>
#include <monad/core/withdrawal.hpp>

#include <cstdint>
#include <utility>
#include <variant>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct MonadVoteV1
{
    bytes32_t id{NULL_HASH_BLAKE3};
    uint64_t round{0};
    uint64_t epoch{0};
    bytes32_t parent_id{NULL_HASH_BLAKE3};
    uint64_t parent_round{0};

    friend bool operator==(MonadVoteV1 const &, MonadVoteV1 const &) = default;
};

struct MonadVoteV2
{
    bytes32_t id{NULL_HASH_BLAKE3};
    uint64_t round{0};
    uint64_t epoch{0};

    friend bool operator==(MonadVoteV2 const &, MonadVoteV2 const &) = default;
};

struct MonadSignerMap
{
    uint32_t num_bits{0};
    byte_string bitmap{};

    friend bool
    operator==(MonadSignerMap const &, MonadSignerMap const &) = default;
};

struct MonadSignatures
{
    MonadSignerMap signer_map{};
    byte_string_fixed<96> aggregate_signature{};

    friend bool
    operator==(MonadSignatures const &, MonadSignatures const &) = default;
};

struct MonadQuorumCertificate
{
    std::variant<MonadVoteV1, MonadVoteV2> vote{};
    MonadSignatures signatures{};

    friend bool operator==(
        MonadQuorumCertificate const &,
        MonadQuorumCertificate const &) = default;
};

struct MonadConsensusBlockHeader
{
    uint64_t block_round{0};
    uint64_t epoch{0};
    MonadQuorumCertificate qc{}; // qc is for the previous block
    byte_string_fixed<33> author{};
    uint64_t seqno{0};
    uint128_t timestamp_ns{0};
    byte_string_fixed<96> round_signature{};
    std::vector<BlockHeader> delayed_execution_results{};
    BlockHeader execution_inputs{};
    bytes32_t block_body_id{NULL_HASH_BLAKE3};

    bytes32_t parent_id() const noexcept
    {
        return std::visit([](auto const &v) { return v.id; }, qc.vote);
    }

    static MonadConsensusBlockHeader from_eth_header(
        BlockHeader const &eth_header,
        std::optional<uint64_t> const round_number = std::nullopt)
    {
        uint64_t const round =
            round_number.has_value() ? round_number.value() : eth_header.number;
        uint64_t const parent_round = round - std::min(round, 1ul);
        uint64_t const grandparent_round = round - std::min(round, 2ul);

        return MonadConsensusBlockHeader{
            .block_round = round,
            .epoch = 0,
            .qc =
                MonadQuorumCertificate{
                    .vote =
                        MonadVoteV1{
                            .id = bytes32_t{parent_round},
                            .round = parent_round,
                            .epoch = 0,
                            .parent_id = bytes32_t{grandparent_round},
                            .parent_round = grandparent_round,
                        },
                    .signatures = {}},
            .author = {},
            .seqno = eth_header.number,
            .timestamp_ns = eth_header.timestamp,
            .round_signature = {},
            .delayed_execution_results = std::vector<BlockHeader>{BlockHeader{
                .number = grandparent_round}},
            .execution_inputs = eth_header,
            .block_body_id = {}};
    }

    friend bool operator==(
        MonadConsensusBlockHeader const &,
        MonadConsensusBlockHeader const &) = default;
};

static_assert(sizeof(MonadConsensusBlockHeader) == 1224);
static_assert(alignof(MonadConsensusBlockHeader) == 8);

struct MonadConsensusBlockBody
{
    std::vector<Transaction> transactions{};
    std::vector<BlockHeader> ommers{};
    std::vector<Withdrawal> withdrawals{};

    friend bool operator==(
        MonadConsensusBlockBody const &,
        MonadConsensusBlockBody const &) = default;
};

static_assert(sizeof(MonadConsensusBlockBody) == 72);
static_assert(alignof(MonadConsensusBlockBody) == 8);

struct MonadConsensusBlock
{
    MonadConsensusBlockHeader header{};
    MonadConsensusBlockBody body{};

    friend bool operator==(
        MonadConsensusBlock const &, MonadConsensusBlock const &) = default;
};

static_assert(sizeof(MonadConsensusBlock) == 1296);
static_assert(alignof(MonadConsensusBlock) == 8);

std::pair<MonadConsensusBlockHeader, bytes32_t>
consensus_header_and_id_from_eth_header(
    BlockHeader const &eth_header,
    std::optional<uint64_t> round_number = std::nullopt);

MONAD_NAMESPACE_END
