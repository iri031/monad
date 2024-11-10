#include <monad/execution/block_hash_buffer.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(BlockHashBuffer, simple_chain)
{
    BlockHashChain chain;
    auto &buffer1 = chain.next_buffer(0, 0, 0);
    buffer1.set(0, bytes32_t{1});
    chain.finalize(0, 0);
    auto &buffer2 = chain.next_buffer(1, 1, 0);
    buffer2.set(1, bytes32_t{2});
    chain.finalize(1, 1);
    auto &buffer3 = chain.next_buffer(2, 2, 1);
    buffer3.set(2, bytes32_t{3});
    chain.finalize(2, 2);

    EXPECT_EQ(buffer3.get(0), bytes32_t{1});
    EXPECT_EQ(buffer3.get(1), bytes32_t{2});
    EXPECT_EQ(buffer3.get(2), bytes32_t{3});
}

TEST(BlockHashBuffer, fork)
{
    BlockHashChain chain;

    auto &buffer1 = chain.next_buffer(0, 0, 0);
    buffer1.set(0, bytes32_t{1});

    // fork at block 1
    auto &buffer2 = chain.next_buffer(1, 1, 0);
    buffer2.set(1, bytes32_t{2});
    auto &buffer3 = chain.next_buffer(1, 2, 0);
    buffer3.set(1, bytes32_t{3});

    // and block 2
    auto &buffer4 = chain.next_buffer(2, 3, 2 /* parent round */);
    buffer4.set(2, bytes32_t{4});
    auto &buffer5 = chain.next_buffer(2, 4, 1 /* parent round */);
    buffer5.set(2, bytes32_t{5});

    // verify two chains are distinct
    EXPECT_EQ(buffer4.get(0), bytes32_t{1});
    EXPECT_EQ(buffer4.get(1), bytes32_t{3});
    EXPECT_EQ(buffer4.get(2), bytes32_t{4});

    EXPECT_EQ(buffer5.get(0), bytes32_t{1});
    EXPECT_EQ(buffer5.get(1), bytes32_t{2});
    EXPECT_EQ(buffer5.get(2), bytes32_t{5});

    // finalize
    chain.finalize(0, 0);
    chain.finalize(1, 2);
    chain.finalize(2, 3);
}
