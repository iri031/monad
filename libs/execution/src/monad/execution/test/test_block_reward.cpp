#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <optional>

using namespace monad;

using db_t = TrieDb;

constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};
constexpr auto b{0x5353535353535353535353535353535353535353_address};
constexpr auto c{0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address};

TEST(BlockReward, apply_block_reward)
{
    // Frontier
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        db_t tdb{db};
        tdb.commit(
            StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
            Code{},
            BlockHeader{});

        BlockState bs{tdb};
        State as{bs, Incarnation{1, 1}};

        EXPECT_TRUE(as.account_exists(a));

        Block const block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward<EVMC_FRONTIER>(as, block);

        EXPECT_EQ(
            intx::be::load<uint256_t>(as.get_balance(a)),
            5'312'500'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(as.get_balance(b)),
            4'375'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(as.get_balance(c)),
            3'750'000'000'000'000'000);
    }

    // Byzantium
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        db_t tdb{db};
        BlockState bs{tdb};
        State as{bs, Incarnation{1, 1}};
        (void)as.get_balance(a);

        EXPECT_FALSE(as.account_exists(a));

        // block award
        Block const block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward<EVMC_BYZANTIUM>(as, block);

        EXPECT_EQ(
            intx::be::load<uint256_t>(as.get_balance(a)),
            3'187'500'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(as.get_balance(b)),
            2'625'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(as.get_balance(c)),
            2'250'000'000'000'000'000);
    }

    // Constantinople_and_petersburg
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        db_t tdb{db};
        BlockState bs{tdb};
        State s{bs, Incarnation{0, 0}};

        Block const block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward<EVMC_PETERSBURG>(s, block);

        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(a)),
            2'125'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(b)),
            1'750'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(c)),
            1'500'000'000'000'000'000);
    }

    // Paris EIP-3675
    {
        Block block{};
        block.header.beneficiary = a;

        InMemoryMachine machine;
        mpt::Db db{machine};
        db_t tdb{db};
        BlockState bs{tdb};
        State s{bs, Incarnation{0, 0}};

        apply_block_reward<EVMC_PARIS>(s, block);

        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(a)), 0u);
    }
}
