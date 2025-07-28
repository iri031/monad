#include <category/execution/monad/fee_buffer.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(FeeBuffer, basic)
{
    FeeBuffer buffer;
    for (unsigned block = 1; block <= 10; ++block) {
        buffer.set(block, bytes32_t{block}, bytes32_t{block - 1});
        for (unsigned addr = 1; addr <= 10; ++addr) {
            buffer.note(addr, Address{addr}, addr * block);
        }
        buffer.propose();

        for (unsigned addr = 1; addr <= 10; ++addr) {
            EXPECT_EQ(
                buffer.get(addr, Address{addr}),
                (FeeBufferResult{
                    .cumulative_fee =
                        uint512_t{
                            (block * addr) +
                            ((block > 1 ? block - 1 : 0) * addr) +
                            ((block > 2 ? block - 2 : 0) * addr)},
                    .tx_fee = uint512_t{addr * block},
                    .num_fees = std::min(block, 3u)}));
        }
    }
}

TEST(FeeBuffer, finalize)
{
    FeeBuffer buffer;
    buffer.set(0, bytes32_t{0}, bytes32_t{0});
    buffer.note(0, Address{1}, 1);
    buffer.propose();

    buffer.set(1, bytes32_t{1}, bytes32_t{0});
    buffer.note(0, Address{1}, 2);
    buffer.propose();

    buffer.set(2, bytes32_t{2}, bytes32_t{1});
    buffer.note(0, Address{1}, 3);
    buffer.propose();

    EXPECT_EQ(
        buffer.get(0, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{6},
            .tx_fee = uint512_t{3},
            .num_fees = 3}));

    buffer.finalize(bytes32_t{2});

    EXPECT_EQ(
        buffer.get(0, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{6},
            .tx_fee = uint512_t{3},
            .num_fees = 3}));

    buffer.set(3, bytes32_t{3}, bytes32_t{2});
    buffer.note(0, Address{1}, 3);
    buffer.propose();
    EXPECT_EQ(
        buffer.get(0, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{8},
            .tx_fee = uint512_t{3},
            .num_fees = 3}));
}

TEST(FeeBuffer, branch)
{
    FeeBuffer buffer;
    buffer.set(10, bytes32_t{10}, bytes32_t{0});
    buffer.note(0, Address{1}, 1);
    buffer.propose();

    buffer.set(11, bytes32_t{11}, bytes32_t{10});
    buffer.note(0, Address{1}, 2);
    buffer.propose();

    buffer.set(11, bytes32_t{12}, bytes32_t{10});
    buffer.note(0, Address{1}, 3);
    buffer.propose();

    EXPECT_EQ(
        buffer.get(0, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{4},
            .tx_fee = uint512_t{3},
            .num_fees = 2}));

    buffer.set(12, bytes32_t{13}, bytes32_t{11});
    buffer.note(0, Address{1}, 2);
    buffer.propose();

    EXPECT_EQ(
        buffer.get(0, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{5},
            .tx_fee = uint512_t{2},
            .num_fees = 3}));
}

TEST(FeeBuffer, cumulative)
{
    FeeBuffer buffer;
    buffer.set(10, bytes32_t{10}, bytes32_t{0});
    buffer.note(0, Address{1}, 1);
    buffer.note(1, Address{1}, 3);
    buffer.propose();

    buffer.set(11, bytes32_t{11}, bytes32_t{10});
    buffer.note(0, Address{1}, 2);
    buffer.note(1, Address{1}, 1);
    buffer.note(2, Address{1}, 10);
    buffer.propose();

    EXPECT_EQ(
        buffer.get(0, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{6},
            .tx_fee = uint512_t{2},
            .num_fees = 3}));
    EXPECT_EQ(
        buffer.get(1, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{7},
            .tx_fee = uint512_t{1},
            .num_fees = 4}));
    EXPECT_EQ(
        buffer.get(2, Address{1}),
        (FeeBufferResult{
            .cumulative_fee = uint512_t{17},
            .tx_fee = uint512_t{10},
            .num_fees = 5}));
}
