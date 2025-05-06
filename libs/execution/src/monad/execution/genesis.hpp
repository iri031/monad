#pragma once

#include <monad/chain/chain_config.h>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_mainnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/evmc.h>
#include <evmc/helpers.h>
#include <evmc/hex.hpp>

#include <nlohmann/json.hpp>

#include <intx/intx.hpp>

#include <algorithm>
#include <fstream>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

// TODO: Different chain_id has different genesis json file (with some of them
// not having certain field)
// Issue #131
inline BlockHeader read_genesis_blockheader(
    nlohmann::json const &genesis_json, evmc_revision const rev)
{
    auto const assert_valid = [&genesis_json, rev](
                                  char const *const field,
                                  evmc_revision const since) {
        bool const present = genesis_json.contains(field);
        if (rev < since) {
            MONAD_ASSERT_PRINTF(
                !present,
                "unexpected %s for revision %s which is only present since %s",
                field,
                evmc_revision_to_string(rev),
                evmc_revision_to_string(since));
        }
        else {
            MONAD_ASSERT_PRINTF(
                present,
                "expected %s is missing for revision %s",
                field,
                evmc_revision_to_string(rev));
        }
    };

    assert_valid("baseFeePerGas", EVMC_LONDON);
    assert_valid("blobGasUsed", EVMC_CANCUN);
    assert_valid("excessBlobGas", EVMC_CANCUN);
    assert_valid("parentBeaconBlockRoot", EVMC_CANCUN);

    BlockHeader block_header{};

    block_header.difficulty = intx::from_string<uint256_t>(
        genesis_json["difficulty"].get<std::string>());

    auto const extra_data =
        evmc::from_hex(genesis_json["extraData"].get<std::string>());
    MONAD_ASSERT(extra_data.has_value());
    block_header.extra_data = extra_data.value();

    block_header.gas_limit =
        std::stoull(genesis_json["gasLimit"].get<std::string>(), nullptr, 0);

    auto const mix_hash_byte_string =
        evmc::from_hex(genesis_json["mixHash"].get<std::string>());
    MONAD_ASSERT(mix_hash_byte_string.has_value());
    std::copy_n(
        mix_hash_byte_string.value().begin(),
        mix_hash_byte_string.value().length(),
        block_header.prev_randao.bytes);

    uint64_t const nonce{
        std::stoull(genesis_json["nonce"].get<std::string>(), nullptr, 0)};
    intx::be::unsafe::store<uint64_t>(block_header.nonce.data(), nonce);

    auto const parent_hash_byte_string =
        evmc::from_hex(genesis_json["parentHash"].get<std::string>());
    MONAD_ASSERT(parent_hash_byte_string.has_value());
    std::copy_n(
        parent_hash_byte_string.value().begin(),
        parent_hash_byte_string.value().length(),
        block_header.parent_hash.bytes);

    block_header.timestamp =
        std::stoull(genesis_json["timestamp"].get<std::string>(), nullptr, 0);

    if (genesis_json.contains("coinbase")) {
        auto const coinbase =
            evmc::from_hex(genesis_json["coinbase"].get<std::string>());
        MONAD_ASSERT(coinbase.has_value());
        std::copy_n(
            coinbase.value().begin(),
            coinbase.value().length(),
            block_header.beneficiary.bytes);
    }

    // London fork
    if (genesis_json.contains("baseFeePerGas")) {
        block_header.base_fee_per_gas = intx::from_string<uint256_t>(
            genesis_json["baseFeePerGas"].get<std::string>());
    }

    // Cancun fork
    if (genesis_json.contains("blobGasUsed")) {
        block_header.blob_gas_used = std::stoull(
            genesis_json["blobGasUsed"].get<std::string>(), nullptr, 0);
    }
    if (genesis_json.contains("excessBlobGas")) {
        block_header.excess_blob_gas = std::stoull(
            genesis_json["excessBlobGas"].get<std::string>(), nullptr, 0);
    }
    if (genesis_json.contains("parentBeaconBlockRoot")) {
        auto const parent_beacon_block_root = evmc::from_hex(
            genesis_json["parentBeaconBlockRoot"].get<std::string>());
        MONAD_ASSERT(parent_beacon_block_root.has_value());
        auto &write_to =
            block_header.parent_beacon_block_root.emplace(bytes32_t{});
        std::copy_n(
            parent_beacon_block_root.value().begin(),
            parent_beacon_block_root.value().length(),
            write_to.bytes);
    }

    return block_header;
}

inline void read_genesis_state(
    nlohmann::json const &genesis_json, StateDeltas &state_deltas)
{
    for (auto const &account_info : genesis_json["alloc"].items()) {
        Address address{};
        auto const address_byte_string =
            evmc::from_hex("0x" + account_info.key());
        MONAD_ASSERT(address_byte_string.has_value());
        std::copy_n(
            address_byte_string.value().begin(),
            address_byte_string.value().length(),
            address.bytes);

        Account account{};
        auto const balance_byte_string =
            account_info.value()["wei_balance"].get<std::string>();
        account.balance = intx::from_string<uint256_t>(balance_byte_string);
        account.nonce = 0u;

        state_deltas.emplace(
            address, StateDelta{.account = {std::nullopt, account}});
    }
}

inline BlockHeader read_genesis(
    std::filesystem::path const &genesis_file, Db &db,
    monad_chain_config const chain_config)
{
    std::ifstream ifile(genesis_file.c_str());
    auto const genesis_json = nlohmann::json::parse(ifile);

    StateDeltas state_deltas;
    read_genesis_state(genesis_json, state_deltas);

    uint64_t const timestamp =
        std::stoull(genesis_json["timestamp"].get<std::string>(), nullptr, 0);
    auto const chain = [chain_config] -> std::unique_ptr<Chain> {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return std::make_unique<EthereumMainnet>();
        case CHAIN_CONFIG_MONAD_DEVNET:
            return std::make_unique<MonadDevnet>();
        case CHAIN_CONFIG_MONAD_TESTNET:
            return std::make_unique<MonadTestnet>();
        case CHAIN_CONFIG_MONAD_MAINNET:
            return std::make_unique<MonadMainnet>();
        }
        MONAD_ASSERT(false);
    }();
    evmc_revision const rev = chain->get_revision(0, timestamp);
    MonadConsensusBlockHeader consensus_header{};
    consensus_header.execution_inputs =
        read_genesis_blockheader(genesis_json, rev);
    db.commit(
        state_deltas,
        Code{},
        consensus_header,
        std::vector<Receipt>{},
        std::vector<std::vector<CallFrame>>{},
        std::vector<Address>{},
        std::vector<Transaction>{},
        std::vector<BlockHeader>{},
        rev < EVMC_SHANGHAI ? std::nullopt
                            : std::make_optional<std::vector<Withdrawal>>());
    db.finalize(0, 0);
    BlockHeader const ret = db.read_eth_header();
    Result<void> const validate = static_validate_header(rev, ret);
    MONAD_ASSERT_PRINTF(
        validate.has_value(),
        "bad genesis header parsed: %s",
        validate.error().message().c_str());
    return ret;
}

MONAD_NAMESPACE_END
