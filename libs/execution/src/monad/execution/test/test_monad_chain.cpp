#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/genesis_state.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_mainnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/chain/monad_testnet2.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/inflight_expenses_buffer.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/mpt/db.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(MonadChain, compute_gas_refund)
{
    MonadTestnet monad_chain;
    Transaction tx{.gas_limit = 21'000};

    BlockHeader before_fork{.number = 0, .timestamp = 0};
    BlockHeader after_fork{.number = 1, .timestamp = 1739559600};

    auto const refund_before_fork = monad_chain.compute_gas_refund(
        before_fork.number, before_fork.timestamp, tx, 20'000, 1000);
    auto const refund_after_fork = monad_chain.compute_gas_refund(
        after_fork.number, after_fork.timestamp, tx, 20'000, 1000);
    EXPECT_EQ(20'200, refund_before_fork - refund_after_fork);
}

TEST(MonadChain, get_max_code_size)
{
    MonadTestnet const chain;
    EXPECT_EQ(chain.get_max_code_size(0, 1739559600), MAX_CODE_SIZE_EIP170);
    EXPECT_EQ(chain.get_max_code_size(0, 1741978800), 128 * 1024);
}

TEST(MonadChain, Genesis)
{
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadTestnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x1436534e54a22183ea29a2273b341cb50018ed066441ffd111cd263297caba35_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_FRONTIER>(header).has_value());
        // the header generated at the time was not a valid header for the
        // cancun revision
        EXPECT_FALSE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }

    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadDevnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0xb711505d8f46fc921ae824f847f26c5c3657bf6c8b9dcf07ffdf3357a143bca9_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_FRONTIER>(header).has_value());
        // the header generated at the time was not a valid header for the
        // cancun revision
        EXPECT_FALSE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadMainnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x0c47353304f22b1c15706367d739b850cda80b5c87bbc335014fef3d88deaac9_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadTestnet2 const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0xFE557D7B2B42D6352B985949AA37EDA10FB02C90FEE62EB29E68839F2FB72B31_bytes32);
        EXPECT_TRUE(static_validate_header<EVMC_CANCUN>(header).has_value());
    }
}

TEST(MonadChain, get_inflight_expense)
{
    Transaction const tx{
        .max_fee_per_gas = 30'000, .gas_limit = 100, .value = 15};

    uint512_t const expected = uint256_t{15} + max_gas_cost(100, 30'000);
    for (monad_revision const rev : {MONAD_ONE, MONAD_TWO}) {
        EXPECT_EQ(get_inflight_expense(rev, tx), expected);
    }
}

TEST(MonadChain, get_max_reserve_balance)
{
    constexpr Address ADDRESS =
        0x0000000000000000000000000000000000000100_address;
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    tdb.commit(
        StateDeltas{
            {ADDRESS, StateDelta{{std::nullopt, Account{.balance = 100}}}}},
        Code{},
        MonadConsensusBlockHeader{});
    for (monad_revision const rev : {MONAD_ONE, MONAD_TWO}) {
        EXPECT_EQ(get_max_reserve_balance(rev, ADDRESS, tdb), 100);
    }
}

TEST(MonadChain, ValidateBlock)
{
    constexpr Address ADDRESS =
        0x0000000000000000000000000000000000000100_address;
    Block const block{.transactions = {Transaction{}}};
    std::vector<Address> const senders{ADDRESS};
    std::vector<uint256_t> const max_reserve_balances{100};
    InflightExpensesBuffer inflight_expenses;

    inflight_expenses.set(0, 0, 0);
    inflight_expenses.add(ADDRESS, 10);
    inflight_expenses.propose();
    EXPECT_TRUE(
        validate_block(block, senders, max_reserve_balances, inflight_expenses)
            .has_value());

    inflight_expenses.set(1, 1, 0);
    inflight_expenses.add(ADDRESS, 95);
    inflight_expenses.propose();
    EXPECT_FALSE(
        validate_block(block, senders, max_reserve_balances, inflight_expenses)
            .has_value());

    inflight_expenses.set(2, 2, 1);
    inflight_expenses.propose();

    inflight_expenses.set(3, 3, 2);
    inflight_expenses.propose();

    EXPECT_TRUE(
        validate_block(block, senders, max_reserve_balances, inflight_expenses)
            .has_value());

    inflight_expenses.set(4, 4, 3);
    inflight_expenses.propose();
}
