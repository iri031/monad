#include <monad/lru/clock.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

using AsyncClock = monad::ClockReplacer<int, int>;

TEST(async_clock_test, insert_and_access)
{
    AsyncClock clock(5);

    clock.insert(1, 0x123);
    clock.insert(2, 0xdead);
    clock.insert(3, 0xbeef);

    EXPECT_EQ(clock.size(), 3);

    auto res = clock.find(3);
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res->get(), 0xbeef);

    res = clock.find(2);
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res->get(), 0xdead);

    res = clock.find(1);
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(res->get(), 0x123);

    clock.insert(4, 0xdead);
    clock.insert(5, 0xbeef);

    EXPECT_EQ(clock.size(), 5);
}

TEST(async_clock_test, recency_evict)
{
    AsyncClock clock(10);

    clock.insert(1, 0x123);
    clock.insert(2, 0xdead);
    clock.insert(3, 0xbeef);
    clock.insert(4, 0xcafe4);
    clock.insert(5, 0x1235);

    clock.insert(6, 0xdead6);
    clock.insert(7, 0xbeef7);
    clock.insert(8, 0xcafe8);
    clock.insert(9, 0xbeef9);
    clock.insert(10, 0xcafee10);
    clock.insert(11, 0xbeeef11);

    EXPECT_EQ(clock.size(), 10);

    // approximates least recently used
    EXPECT_EQ(clock.find(2)->get(), 0xdead);
    EXPECT_EQ(clock.find(3)->get(), 0xbeef);
    EXPECT_EQ(clock.find(4)->get(), 0xcafe4);
    EXPECT_EQ(clock.find(5)->get(), 0x1235);
    EXPECT_EQ(clock.find(6)->get(), 0xdead6);
    EXPECT_EQ(clock.find(7)->get(), 0xbeef7);
    EXPECT_EQ(clock.find(8)->get(), 0xcafe8);
    EXPECT_EQ(clock.find(9)->get(), 0xbeef9);
    EXPECT_EQ(clock.find(10)->get(), 0xcafee10);
    EXPECT_EQ(clock.find(11)->get(), 0xbeeef11);

    EXPECT_FALSE(clock.find(1));

    clock.insert(2, 0xc0ffee);
    clock.insert(12, 100);

    EXPECT_EQ(clock.size(), 10);
    EXPECT_EQ(clock.find(2)->get(), 0xc0ffee);
    EXPECT_EQ(clock.find(12)->get(), 100);

    EXPECT_FALSE(clock.find(3));
}

TEST(async_clock_test, repeated_access)
{
    AsyncClock clock(10);

    clock.insert(1, 0x123);
    clock.insert(2, 0xdead);
    clock.insert(3, 0xbeef);
    clock.insert(4, 0xcafe4);
    clock.insert(5, 0x1235);
    clock.insert(6, 0xdead6);
    clock.insert(7, 0xbeef7);
    clock.insert(8, 0xcafe8);
    clock.insert(9, 0xbeef9);
    clock.insert(10, 0xcafee10);

    EXPECT_EQ(clock.size(), 10);

    ASSERT_TRUE(clock.find(1));
    ASSERT_TRUE(clock.find(1));
    ASSERT_TRUE(clock.find(3));
    ASSERT_TRUE(clock.find(3));
    ASSERT_TRUE(clock.find(4));
    ASSERT_TRUE(clock.find(4));
    ASSERT_TRUE(clock.find(5));
    ASSERT_TRUE(clock.find(5));
    ASSERT_TRUE(clock.find(6));
    ASSERT_TRUE(clock.find(6));
    ASSERT_TRUE(clock.find(7));
    ASSERT_TRUE(clock.find(7));
    ASSERT_TRUE(clock.find(8));
    ASSERT_TRUE(clock.find(8));

    clock.insert(11, 0xbeeef11);
    clock.insert(12, 0xbeeef12);
    clock.insert(13, 0xbeeef13);

    EXPECT_EQ(clock.size(), 10);

    EXPECT_FALSE(clock.find(2));
    EXPECT_FALSE(clock.find(9));
    EXPECT_FALSE(clock.find(10));

    ASSERT_TRUE(clock.find(11));
    ASSERT_TRUE(clock.find(12));
    ASSERT_TRUE(clock.find(13));

    EXPECT_EQ(clock.size(), 10);
}

TEST(async_clock_test, scan_pattern_resistance)
{
    AsyncClock clock(10);

    for (int i = 1; i <= 10; i++) {
        clock.insert(i, i * 0x100);
    }
    EXPECT_EQ(clock.size(), 10);
    // scan key 9-16 repeatedly
    for (auto scan = 0; scan < 3; scan++) {
        for (int i = 9; i <= 16; i++) {
            clock.insert(i, i * 0x100 + scan);
        }
    }

    int survivors = 0;

    for (int i = 1; i <= 10; i++) {
        if (clock.find(i)) {
            survivors++;
        }
    }

    EXPECT_GT(survivors, 0);
}

TEST(async_clock_test, loop_pattern)
{
    AsyncClock clock(10);
    for (int i = 1; i <= 10; i++) {
        clock.insert(i, i * 0x200);
    }
    // loop over 9-12 and try to evict popular
    for (int loop = 0; loop < 5; loop++) {
        for (int i = 9; i <= 12; i++) {
            clock.insert(i, i * 0x200 + loop);
            clock.find(i);
        }
    }

    int survivors = 0;
    for (int i = 1; i <= 8; i++) {
        if (clock.find(i)) {
            survivors++;
        }
    }

    EXPECT_GT(survivors, 4);
}

TEST(async_clock_test, sequential_scan)
{
    AsyncClock clock(6);

    clock.insert(1, 0x111);
    clock.insert(2, 0x222);
    clock.insert(3, 0x333);

    for (int i = 0; i < 3; i++) {
        clock.find(1);
        clock.find(2);
        clock.find(3);
    }

    for (int i = 10; i <= 20; i++) {
        clock.insert(i, i * 0x100);
    }

    int hot_items_survived = 0;
    if (clock.find(1)) {
        hot_items_survived++;
    }
    if (clock.find(2)) {
        hot_items_survived++;
    }
    if (clock.find(3)) {
        hot_items_survived++;
    }

    EXPECT_GT(hot_items_survived, 0);
    EXPECT_EQ(clock.size(), 6);
}
