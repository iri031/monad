#include <monad/core/rlp/int_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/monad_precompiles.hpp>
#include <monad/mpt/db.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

using namespace monad;

TEST(MonadPrecompiles, max_reserve_balance_support)
{
    constexpr Address ADDRESS{1};
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};
    byte_string get_data(1 + sizeof(Address), '0');
    get_data[0] = 0x2;
    std::memcpy(&get_data[1], ADDRESS.bytes, sizeof(Address));
    evmc_message const msg{
        .depth = 0,
        .gas = 100'000,
        .sender = ADDRESS,
        .input_data = get_data.data(),
        .input_size = get_data.size(),
        .code_address = MAX_RESERVE_BALANCE_ADDRESS};

    for (auto const rev : {MONAD_ZERO, MONAD_ONE, MONAD_TWO}) {
        EXPECT_FALSE(check_call_monad_precompile(rev, msg, state).has_value());
    }
    EXPECT_TRUE(
        check_call_monad_precompile(MONAD_THREE, msg, state).has_value());
}

TEST(MonadPrecompiles, max_reserve_balance)
{
    constexpr Address ADDRESS{1};
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};

    byte_string get_data(1 + sizeof(Address), '0');
    get_data[0] = 0x2;
    std::memcpy(&get_data[1], ADDRESS.bytes, sizeof(Address));

    { // get
        evmc_message const msg{
            .depth = 0,
            .gas = 100'000,
            .sender = ADDRESS,
            .input_data = get_data.data(),
            .input_size = get_data.size(),
            .code_address = MAX_RESERVE_BALANCE_ADDRESS};
        auto const result =
            check_call_monad_precompile(MONAD_THREE, msg, state);
        ASSERT_TRUE(result.has_value());
        ASSERT_EQ(result.value().status_code, EVMC_SUCCESS);
        byte_string_view output{
            result.value().output_data, result.value().output_size};
        auto const decode_result = rlp::decode_unsigned<uint256_t>(output);
        ASSERT_TRUE(decode_result.has_value());
        EXPECT_EQ(decode_result.value(), 0);
    }

    { // set
        byte_string set_data = {0x1};
        set_data += rlp::encode_unsigned(uint256_t{10'000});
        evmc_message const msg{
            .depth = 0,
            .gas = 100'000,
            .sender = ADDRESS,
            .input_data = set_data.data(),
            .input_size = set_data.size(),
            .code_address = MAX_RESERVE_BALANCE_ADDRESS};
        auto const result =
            check_call_monad_precompile(MONAD_THREE, msg, state);
        ASSERT_TRUE(result.has_value());
        ASSERT_EQ(result.value().status_code, EVMC_SUCCESS);
        byte_string_view output{
            result.value().output_data, result.value().output_size};
        auto const decode_result = rlp::decode_unsigned<uint256_t>(output);
        ASSERT_TRUE(decode_result.has_value());
        EXPECT_EQ(decode_result.value(), 0);
    }

    { // get
        evmc_message const msg{
            .depth = 0,
            .gas = 100'000,
            .sender = ADDRESS,
            .input_data = get_data.data(),
            .input_size = get_data.size(),
            .code_address = MAX_RESERVE_BALANCE_ADDRESS};
        auto const result =
            check_call_monad_precompile(MONAD_THREE, msg, state);
        ASSERT_TRUE(result.has_value());
        ASSERT_EQ(result.value().status_code, EVMC_SUCCESS);
        byte_string_view output{
            result.value().output_data, result.value().output_size};
        auto const decode_result = rlp::decode_unsigned<uint256_t>(output);
        ASSERT_TRUE(decode_result.has_value());
        EXPECT_EQ(decode_result.value(), 10'000);
    }

    { // set
        byte_string set_data = {0x1};
        set_data += rlp::encode_unsigned(uint256_t{100'000});
        evmc_message const msg{
            .depth = 0,
            .gas = 100'000,
            .sender = ADDRESS,
            .input_data = set_data.data(),
            .input_size = set_data.size(),
            .code_address = MAX_RESERVE_BALANCE_ADDRESS};
        auto const result =
            check_call_monad_precompile(MONAD_THREE, msg, state);
        ASSERT_TRUE(result.has_value());
        ASSERT_EQ(result.value().status_code, EVMC_SUCCESS);
        byte_string_view output{
            result.value().output_data, result.value().output_size};
        auto const decode_result = rlp::decode_unsigned<uint256_t>(output);
        ASSERT_TRUE(decode_result.has_value());
        EXPECT_EQ(decode_result.value(), 10'000);
    }

    { // get
        evmc_message const msg{
            .depth = 0,
            .gas = 100'000,
            .sender = ADDRESS,
            .input_data = get_data.data(),
            .input_size = get_data.size(),
            .code_address = MAX_RESERVE_BALANCE_ADDRESS};
        auto const result =
            check_call_monad_precompile(MONAD_THREE, msg, state);
        ASSERT_TRUE(result.has_value());
        ASSERT_EQ(result.value().status_code, EVMC_SUCCESS);
        byte_string_view output{
            result.value().output_data, result.value().output_size};
        auto const decode_result = rlp::decode_unsigned<uint256_t>(output);
        ASSERT_TRUE(decode_result.has_value());
        EXPECT_EQ(decode_result.value(), 100'000);
    }
}
