#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <monad/vm/vm.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::test;

struct Storage : public ::testing::Test
{
    static constexpr auto ADDRESS{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};

    void SetUp() override
    {
        commit_sequential(
            tdb,
            StateDeltas{
                {ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 1, .nonce = 1}}}}},
            Code{},
            BlockHeader{});
        state.touch(ADDRESS);
    }
};

TEST_F(Storage, big_endian)
{
    bytes32_t y{5};
    u256_be be = std::bit_cast<u256_be>(y);
    be = be.native() + 5;
    EXPECT_EQ(std::bit_cast<bytes32_t>(be), bytes32_t{10});
}

TEST_F(Storage, variable)
{
    StorageVariable<uint256_t> var(state, ADDRESS, bytes32_t{6000});
    ASSERT_FALSE(var.load_checked().has_value());
    var.store(5);
    ASSERT_TRUE(var.load_checked().has_value());
    EXPECT_EQ(var.load(), 5);
    var.store(2000);
    EXPECT_EQ(var.load(), 2000);
    var.clear();
    EXPECT_FALSE(var.load_checked().has_value());
}

TEST_F(Storage, struct)
{
    struct S
    {
        int x;
        int y;
        uint256_t z;
    };

    StorageVariable<S> var(state, ADDRESS, bytes32_t{6000});

    ASSERT_FALSE(var.load_checked().has_value());
    var.store(S{.x = 4, .y = 5, .z = 6});
    ASSERT_TRUE(var.load_checked().has_value());
    S s = var.load();
    EXPECT_EQ(s.x, 4);
    EXPECT_EQ(s.y, 5);
    EXPECT_EQ(s.z, uint256_t(6));
    s.x *= 2;
    s.y *= 2;
    s.z *= 2;
    var.store(s);
    ASSERT_TRUE(var.load_checked().has_value());
    S s2 = var.load();
    EXPECT_EQ(s2.x, 8);
    EXPECT_EQ(s2.y, 10);
    EXPECT_EQ(s2.z, 12);
    var.clear();
    EXPECT_FALSE(var.load_checked());
}

TEST_F(Storage, array)
{
    struct SomeType
    {
        uint256_t blob;
        uint32_t counter;
    };

    StorageArray<SomeType> arr(state, ADDRESS, bytes32_t{100});
    EXPECT_EQ(arr.length(), 0);

    for (uint32_t i = 0; i < 100; ++i) {
        arr.push(SomeType{.blob = uint256_t{2000}, .counter = i});
        EXPECT_EQ(arr.length(), i + 1);
    }

    for (uint32_t i = 0; i < 100; ++i) {
        auto const res = arr.get(i);
        ASSERT_TRUE(res.load_checked().has_value())
            << "Could not load at index: " << i << std::endl;
        EXPECT_EQ(res.load().counter, i);
    }

    for (uint32_t i = 100; i > 0; --i) {
        arr.pop();
        EXPECT_EQ(arr.length(), i - 1);
    }
}

TEST_F(Storage, pop_empty_array)
{
    StorageArray<uint64_t> arr(state, ADDRESS, bytes32_t{100});
    for (int i = 0; i < 100; ++i) {
        EXPECT_EQ(arr.length(), 0);
        EXPECT_EQ(arr.pop(), 0);
    }
}

TEST_F(Storage, partial_slot)
{

    StorageVariable<u64_be>::Adapter adapter(u64_be{0xABCD});
    bytes32_t expected{};
    expected.bytes[6] = 0xAB;
    expected.bytes[7] = 0xCD;
    EXPECT_EQ(adapter.slots[0], expected);
}
