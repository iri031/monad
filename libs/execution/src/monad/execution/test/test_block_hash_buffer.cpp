#include <monad/execution/block_hash_buffer.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(BlockHashBuffer, simple_chain)
{
    BlockHashBuffer buf;
    BlockHashChain chain(buf);

    uint64_t round = 0;
    uint64_t parent_round = 0;
    chain.propose(bytes32_t{1}, round, parent_round);
    chain.finalize(round);

    ++round;
    chain.propose(bytes32_t{2}, round, parent_round);
    chain.finalize(round);

    ++round;
    ++parent_round;
    chain.propose(bytes32_t{3}, round, parent_round);
    chain.finalize(round);

    EXPECT_EQ(buf.n(), 3);
    EXPECT_EQ(buf.get(0), bytes32_t{1});
    EXPECT_EQ(buf.get(1), bytes32_t{2});
    EXPECT_EQ(buf.get(2), bytes32_t{3});
}

TEST(BlockHashBuffer, fork)
{
    BlockHashBuffer buf;
    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 0 /* round */, 0 /* parent_round */);
    chain.finalize(0);

    // fork at block 1
    chain.propose(bytes32_t{2}, 1 /* round */, 0 /* parent_round */);
    chain.propose(bytes32_t{3}, 2 /* round */, 0 /* parent_round */);

    // fork continues on block 2
    auto const &fork1 =
        chain.propose(bytes32_t{4}, 3 /* round */, 2 /* parent_round */);
    auto const &fork2 =
        chain.propose(bytes32_t{5}, 4 /* round */, 1 /* parent_round */);

    // check the forks are distinct
    EXPECT_EQ(fork1.n(), 3);
    EXPECT_EQ(fork1.get(0), bytes32_t{1});
    EXPECT_EQ(fork1.get(1), bytes32_t{3});
    EXPECT_EQ(fork1.get(2), bytes32_t{4});

    EXPECT_EQ(fork1.n(), 3);
    EXPECT_EQ(fork2.get(0), bytes32_t{1});
    EXPECT_EQ(fork2.get(1), bytes32_t{2});
    EXPECT_EQ(fork2.get(2), bytes32_t{5});

    // ... and that the finalized chain is unmodified
    EXPECT_EQ(buf.n(), 1);

    // finalize chain {0, 1, 4}
    chain.finalize(1);
    chain.finalize(4);

    // finalized chain should match fork
    EXPECT_EQ(buf.n(), 3);
    EXPECT_EQ(buf.get(0), bytes32_t{1});
    EXPECT_EQ(buf.get(1), bytes32_t{2});
    EXPECT_EQ(buf.get(2), bytes32_t{5});
}

TEST(BlockHashBuffer, keep_latest_duplicate)
{
    BlockHashBuffer buf;
    BlockHashChain chain(buf);

    chain.propose(bytes32_t{1}, 0 /* round */, 0 /* parent_round */);
    chain.finalize(0);

    chain.propose(bytes32_t{2}, 1 /* round */, 0 /* parent_round */);
    chain.propose(bytes32_t{3}, 2 /* round */, 0 /* parent_round */);
    chain.propose(bytes32_t{4}, 1 /* round */, 0 /* parent_round */);
    chain.finalize(1);

    EXPECT_EQ(buf.n(), 2);
    EXPECT_EQ(buf.get(0), bytes32_t{1});
    EXPECT_EQ(buf.get(1), bytes32_t{4});
}
