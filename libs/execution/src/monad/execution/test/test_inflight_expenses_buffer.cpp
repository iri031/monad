#include <monad/execution/inflight_expenses_buffer.hpp>

#include <gtest/gtest.h>

using namespace monad;

TEST(InflightExpensesBuffer, basic)
{
    InflightExpensesBuffer buffer;
    for (unsigned block = 0; block < 10; ++block) {
        buffer.set(block, block, block == 0 ? 0 : block - 1);
        for (unsigned addr = 0; addr < 10; ++addr) {
            buffer.add(Address{addr}, uint256_t{addr * block});
        }
        buffer.propose();

        for (unsigned addr = 0; addr < 10; ++addr) {
            EXPECT_EQ(
                buffer.sum(Address{addr}),
                uint256_t{
                    (block * addr) + ((block > 1 ? block - 1 : 0) * addr) +
                    ((block > 2 ? block - 2 : 0) * addr)});
        }
    }
}

TEST(InflightExpensesBuffer, empty)
{
    InflightExpensesBuffer buffer;
    for (unsigned block = 0; block < 10; ++block) {
        buffer.set(block, block, block == 0 ? 0 : block - 1);
        buffer.propose();
    }
    EXPECT_EQ(buffer.sum(Address{1}), 0);
}

TEST(InflightExpensesBuffer, finalize)
{
    InflightExpensesBuffer buffer;
    buffer.set(0, 0, 0);
    buffer.add(Address{1}, 1);
    buffer.propose();

    buffer.set(1, 1, 0);
    buffer.add(Address{1}, 2);
    buffer.propose();

    buffer.set(2, 2, 1);
    buffer.add(Address{1}, 3);
    buffer.propose();

    EXPECT_EQ(buffer.sum(Address{1}), 6);

    buffer.finalize(2);

    EXPECT_EQ(buffer.sum(Address{1}), 6);

    buffer.set(3, 3, 2);
    buffer.add(Address{1}, 3);
    buffer.propose();
    EXPECT_EQ(buffer.sum(Address{1}), 8);
}

TEST(InflightExpensesBuffer, branch)
{
    InflightExpensesBuffer buffer;
    buffer.set(10, 10, 0);
    buffer.add(Address{1}, 1);
    buffer.propose();

    buffer.set(11, 11, 10);
    buffer.add(Address{1}, 2);
    buffer.propose();

    buffer.set(11, 12, 10);
    buffer.add(Address{1}, 3);
    buffer.propose();

    EXPECT_EQ(buffer.sum(Address{1}), 4);

    buffer.set(12, 13, 11);
    buffer.add(Address{1}, 2);
    buffer.propose();

    EXPECT_EQ(buffer.sum(Address{1}), 5);
}
