#include <monad/chain/chain_config.h>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/int_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/log_level_map.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <boost/core/demangle.hpp>

#include <CLI/CLI.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <nlohmann/adl_serializer.hpp>
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

using namespace monad;
namespace fs = std::filesystem;

template <typename T>
[[nodiscard]] T integer_from_json(nlohmann::json const &j)
    requires std::is_same_v<T, int64_t> || std::is_same_v<T, uint64_t>
{
    auto error_message = [&j](auto message_suffix) {
        return fmt::format(
            "integer_from_json<{}> was called with {}, "
            "json_type: {}, error: {}",
            boost::core::demangle(typeid(T).name()),
            j.dump(),
            j.type_name(),
            message_suffix);
    };

    if (j.is_string()) {
        auto const string = j.get<std::string>();
        T value;

        if (string.starts_with("0x")) {
            std::string_view trimmed{string};
            trimmed.remove_prefix(2);
            auto const begin = trimmed.data();
            auto const end = trimmed.data() + trimmed.size();
            auto const parse_result =
                std::from_chars(begin, end, value, 16 /* hex */);
            if (parse_result.ptr != end) {
                throw std::invalid_argument{error_message(
                    "std::from_chars did not fully consume the input")};
            }
            if (parse_result.ec == std::errc{}) {
                return value;
            }
            // I hope SSO makes this OK
            std::string error_code_message;
            if (parse_result.ec == std::errc::invalid_argument) {
                error_code_message = "invalid_argument";
            }
            else if (parse_result.ec == std::errc::result_out_of_range) {
                error_code_message = "result_out_of_range";
            }
            else {
                error_code_message = "unknown";
            }
            throw std::invalid_argument{error_message(fmt::format(
                "std::from_chars failed with {} error code",
                error_code_message))};
        }
        throw std::invalid_argument{
            error_message("non-empty hexadecimal strings are supported")};
    }
    else if (j.is_number_integer()) {
        auto const value = j.get<nlohmann::json::number_float_t>();
        if (j.is_number_unsigned()) {
            if constexpr (std::is_same_v<T, uint64_t>) {
                if (value >= 0) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{
                    error_message("could not convert a negative double to an "
                                  "unsigned integer")};
            }
            else /* if constexpr(std::is_same_v<T, int64_t>) */ {
                if (value >= std::numeric_limits<T>::min() &&
                    value <=
                        static_cast<double>(std::numeric_limits<T>::max())) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{error_message(
                    "unsigned double did not fit into a int64_t")};
            }
        }
        else {
            if constexpr (std::is_same_v<T, uint64_t>) {
                if (value >= std::numeric_limits<T>::min() &&
                    value <=
                        static_cast<double>(std::numeric_limits<T>::max())) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{
                    error_message("converting a signed double to an unsigned "
                                  "integer is not supported")};
            }
            else /* if constexpr(std::is_same_v<T, int64_t>) */ {
                if (value >= std::numeric_limits<T>::min() &&
                    value <=
                        static_cast<double>(std::numeric_limits<T>::max())) {
                    return static_cast<T>(value);
                }
                throw std::invalid_argument{
                    error_message("signed double did not fit into a int64_t")};
            }
        }
    }
    throw std::invalid_argument{
        error_message("only string or integer values are allowed")};
}

namespace nlohmann
{
    template <>
    struct adl_serializer<monad::Address>
    {
        static void from_json(nlohmann::json const &json, monad::Address &o)
        {
            auto const maybe_address =
                evmc::from_hex<monad::Address>(json.get<std::string>());
            if (!maybe_address) {
                throw std::invalid_argument{fmt::format(
                    "failed to convert json object {} to hexadecimal using "
                    "evm::from_hex<monad::address_t>",
                    json.dump())};
            }
            o = maybe_address.value();
        }
    };

    template <>
    struct adl_serializer<monad::uint128_t>
    {
        static void from_json(nlohmann::json const &json, monad::uint128_t &o)
        {
            o = intx::from_string<monad::uint128_t>(json.get<std::string>());
        }
    };

    template <>
    struct adl_serializer<monad::byte_string>
    {
        static void from_json(nlohmann::json const &json, monad::byte_string &o)
        {
            auto const maybe_byte_string =
                evmc::from_hex(json.get<std::string>());
            if (!maybe_byte_string) {
                throw std::invalid_argument{fmt::format(
                    "failed to convert json object {} to hexadecimal using "
                    "evm::from_hex<monad::byte_string>",
                    json.dump())};
            }
            o = maybe_byte_string.value();
        }
    };

    template <>
    struct adl_serializer<monad::bytes32_t>
    {
        static void from_json(nlohmann::json const &json, monad::bytes32_t &o)
        {
            auto const maybe_bytes32 =
                evmc::from_hex<monad::bytes32_t>(json.get<std::string>());
            if (!maybe_bytes32) {
                throw std::invalid_argument{fmt::format(
                    "failed to convert json object {} to hexadecimal using "
                    "evm::from_hex<monad::bytes32_t>",
                    json.dump())};
            }
            o = maybe_bytes32.value();
        }
    };

    template <>
    struct adl_serializer<monad::AccessList>
    {
        static void from_json(nlohmann::json const &j, monad::AccessList &o)
        {
            for (auto const &a : j) {
                std::vector<monad::bytes32_t> storage_access_list;
                for (auto const &storage_key : a.at("storageKeys")) {
                    storage_access_list.emplace_back(
                        storage_key.get<monad::bytes32_t>());
                }
                o.emplace_back(
                    a.at("address").get<monad::Address>(),
                    std::move(storage_access_list));
            }
        }
    };

    template <>
    struct adl_serializer<monad::uint256_t>
    {
        static void from_json(nlohmann::json const &json, monad::uint256_t &o)
        {
            o = intx::from_string<monad::uint256_t>(json.get<std::string>());
        }
    };

    template <>
    struct adl_serializer<monad::TransactionError>
    {
        static void
        from_json(nlohmann::json const &j, monad::TransactionError &error)
        {
            using typename monad::TransactionError;

            auto const str = j.get<std::string>();
            if (str == "TR_InitCodeLimitExceeded") {
                error = TransactionError::InitCodeLimitExceeded;
            }
            else if (str == "TR_NonceHasMaxValue") {
                error = TransactionError::NonceExceedsMax;
            }
            else if (str == "TR_IntrinsicGas") {
                error = TransactionError::IntrinsicGasGreaterThanLimit;
            }
            else if (str == "TR_FeeCapLessThanBlocks") {
                error = TransactionError::MaxFeeLessThanBase;
            }
            else if (str == "TR_GasLimitReached") {
                error = TransactionError::GasLimitReached;
            }
            else if (str == "TR_NoFunds") {
                error = TransactionError::InsufficientBalance;
            }
            else if (str == "TR_TipGtFeeCap") {
                error = TransactionError::PriorityFeeGreaterThanMax;
            }
            else if (str == "TR_TypeNotSupported") {
                error = TransactionError::TypeNotSupported;
            }
            else if (str == "SenderNotEOA") {
                error = TransactionError::SenderNotEoa;
            }
            else {
                // unhandled exception type
                MONAD_ASSERT(false);
            }
        }
    };
}


void load_state_from_json(nlohmann::json const &j, State &state)
{
    for (auto const &[j_addr, j_acc] : j.items()) {
        auto const account_address =
            evmc::from_hex<monad::Address>(j_addr).value();

        if (j_acc.contains("code") || j_acc.contains("storage")) {
            ASSERT_TRUE(j_acc.contains("code") && j_acc.contains("storage"));
            state.create_contract(account_address);
        }

        if (j_acc.contains("code")) {
            state.set_code(
                account_address, j_acc.at("code").get<monad::byte_string>());
        }

        state.add_to_balance(
            account_address, j_acc.at("balance").get<intx::uint256>());
        // we cannot use the nlohmann::json from_json<uint64_t> because
        // it does not use the strtoull implementation, whereas we need
        // it so we can turn a hex string into a uint64_t
        state.set_nonce(
            account_address, integer_from_json<uint64_t>(j_acc.at("nonce")));

        if (j_acc.contains("storage")) {
            ASSERT_TRUE(j_acc["storage"].is_object());
            for (auto const &[key, value] : j_acc["storage"].items()) {
                nlohmann::json const key_json = key;
                monad::bytes32_t const key_bytes32 =
                    key_json.get<monad::bytes32_t>();
                monad::bytes32_t const value_bytes32 = value;
                if (value_bytes32 == monad::bytes32_t{}) {
                    // skip setting starting storage to zero to avoid pointless
                    // deletion
                    continue;
                }
                EXPECT_EQ(
                    state.set_storage(
                        account_address, key_bytes32, value_bytes32),
                    EVMC_STORAGE_ADDED);
            }
        }
    }
}

int main(int const argc, char const *argv[])
{
    CLI::App cli{"gen"};
    cli.option_defaults()->always_capture_default();

    fs::path genesis;
    fs::path chain;

    cli.add_option("--genesis", genesis, "genesis file")
        ->check(CLI::ExistingFile);
    cli.add_option("--chain", chain, "chain.rlp file")
        ->check(CLI::ExistingFile);

    // Initialize triedb (name it as test.db)
    auto const path = [] {
        std::filesystem::path dbname("test.db");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        return dbname;
    }();

    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    TrieDb tdb{db};

    // parse genesis.json
    std::ifstream f(genesis);
    auto const genesis_json = nlohmann::json::parse(f);

    auto const genesis_header = read_genesis_blockheader(genesis_json);

    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};
    load_state_from_json(genesis_json["alloc"], state);
    bs.commit(genesis_header, {}, {}, {}, {}, {}, std::nullopt);

    // read chain.rlp and decode it
    BlockHashBufferFinalized block_hash_buffer;
    std::ifstream ifile(chain);
    
}