// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet2.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/mpt/db.hpp>

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

TEST(MonadChain, create_inside_delegated)
{
    EXPECT_FALSE(MonadMainnet{}.get_create_inside_delegated());
    EXPECT_FALSE(MonadDevnet{}.get_create_inside_delegated());
    EXPECT_FALSE(MonadTestnet{}.get_create_inside_delegated());
    EXPECT_FALSE(MonadTestnet2{}.get_create_inside_delegated());
    EXPECT_TRUE(EthereumMainnet{}.get_create_inside_delegated());
}

void run_revert_transaction_test(
    bool const can_dip, uint64_t const initial_balance_mon,
    uint64_t const gas_fee_mon, uint64_t const value_mon, bool const expected)
{
    constexpr uint256_t BASE_FEE_PER_GAS = 10;
    constexpr Address SENDER{1};
    MonadDevnet const chain;
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};

    ASSERT_EQ(
        monad_default_max_reserve_balance_mon(chain.get_monad_revision(0, 0)),
        100);

    // Set up initial state
    {
        State state{bs, Incarnation{0, 0}};
        uint256_t const initial_balance =
            uint256_t{initial_balance_mon} * 1000000000000000000ULL;
        state.add_to_balance(SENDER, initial_balance);
        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
    }

    uint256_t const gas_fee = uint256_t{gas_fee_mon} * 1000000000000000000ULL;
    uint256_t const gas_limit = gas_fee / BASE_FEE_PER_GAS;
    MONAD_ASSERT(
        (gas_fee % BASE_FEE_PER_GAS) == 0 &&
        gas_limit <= std::numeric_limits<uint64_t>::max());

    Transaction const tx{
        .max_fee_per_gas = BASE_FEE_PER_GAS,
        .gas_limit = uint64_t{gas_limit},
        .type = TransactionType::legacy,
        .max_priority_fee_per_gas = 0,
    };

    std::vector<Address> senders_0;
    if (!can_dip) {
        senders_0.emplace_back(SENDER);
    }
    std::vector<Address> senders_1;
    std::vector<Address> senders_2 = {SENDER};
    std::vector<std::vector<Address>> authorization_lists;
    std::vector<std::vector<Address>> authorization_lists_2 = {{}};

    MonadChainContext chain_context{
        .senders_per_block =
            {std::cref(senders_0), std::cref(senders_1), std::cref(senders_2)},
        .authorization_lists_per_block = {
            std::cref(authorization_lists),
            std::cref(authorization_lists),
            std::cref(authorization_lists_2)}};

    {
        State state{bs, Incarnation{1, 0}};
        state.subtract_from_balance(SENDER, gas_fee);
        uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
        state.subtract_from_balance(SENDER, value);
        bool should_revert = chain.revert_transaction(
            1, // block_number
            0, // timestamp
            SENDER,
            tx,
            BASE_FEE_PER_GAS,
            0, // transaction index
            state,
            &chain_context);

        EXPECT_EQ(should_revert, expected);
    }
}

TEST(MonadChain, revert_transaction_no_dip_gas_fee_with_no_value_false)
{
    run_revert_transaction_test(
        false, // can_dip
        100, // initial balance (MON)
        20, // gas fee (MON)
        0, // value (MON)
        false // expected should_revert
    );

    // now spend whole reserve
    run_revert_transaction_test(
        false, // can_dip
        100, // initial balance (MON)
        100, // gas fee (MON)
        0, // value (MON)
        false // expected should_revert
    );
}

TEST(MonadChain, revert_transaction_no_dip_gas_fee_with_value_true)
{
    run_revert_transaction_test(
        false, // can_dip
        100, // initial balance (MON)
        20, // gas fee (MON)
        1, // value (MON)
        true // expected should_revert
    );

    run_revert_transaction_test(
        false, // can_dip
        150, // initial balance (MON)
        50, // gas fee (MON)
        60, // value (MON)
        true // expected should_revert
    );
}

TEST(MonadChain, revert_transaction_no_dip_gas_fee_with_value_false)
{
    run_revert_transaction_test(
        false, // can_dip
        150, // initial balance (MON)
        50, // gas fee (MON)
        50, // value (MON)
        false // expected should_revert
    );
}

TEST(MonadChain, revert_transaction_dip_false)
{
    run_revert_transaction_test(
        true, // can_dip
        100, // initial balance (MON)
        100, // gas fee (MON)
        0, // value (MON)
        false // expected should_revert
    );

    run_revert_transaction_test(
        true, // can_dip
        100, // initial balance (MON)
        10, // gas fee (MON)
        90, // value (MON)
        false // expected should_revert
    );
}
