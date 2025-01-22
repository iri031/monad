#include <monad/core/blake3.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/emitter/block_emitter.hpp>
#include <monad/emitter/replay_emitter.hpp>
#include <monad/emitter/wal_action.h>
#include <monad/emitter/wal_emitter.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <test_resource_data.h>

#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <limits>
#include <stdlib.h>
#include <unistd.h>

using namespace monad;

namespace
{
    std::string to_hex(uint64_t val)
    {
        bytes32_t as_bytes{val};
        byte_string_view view{as_bytes};
        return evmc::hex(view);
    }
}

class BlockEmitterTestFixture : public ::testing::Test
{
protected:
    std::ofstream wal_os;
    std::filesystem::path ledger_dir;

    void write_dummy_block(uint64_t const round)
    {
        MonadConsensusBlockBody body;
        MonadConsensusBlockHeader header;
        header.block_body_id =
            to_bytes(blake3(rlp::encode_consensus_block_body(body)));
        header.round = round;

        std::ofstream header_os{ledger_dir / (to_hex(round) + ".header")};
        std::ofstream body_os{
            ledger_dir / (evmc::hex(header.block_body_id) + ".body")};
        auto const encoded_body = rlp::encode_consensus_block_body(body);
        auto const encoded_header = rlp::encode_consensus_block_header(header);
        body_os.write(
            reinterpret_cast<char const *>(encoded_body.data()),
            static_cast<std::streamsize>(encoded_body.size()));
        header_os.write(
            reinterpret_cast<char const *>(encoded_header.data()),
            static_cast<std::streamsize>(encoded_header.size()));
        body_os.flush();
        header_os.flush();
    }

    void append_entry(monad_wal_action_type const action, uint64_t const round)
    {
        // write to wal
        monad_wal_action const a{.action = action, .id = bytes32_t{round}};
        wal_os.write(
            reinterpret_cast<char const *>(&a), sizeof(monad_wal_action));
        wal_os.flush();
        write_dummy_block(round);
    }

    void SetUp() override
    {
        char fixture_template[] = "monad_block_emitter_fixture_XXXXXX";
        char *temppath = mkdtemp(fixture_template);
        MONAD_ASSERT(temppath != nullptr);
        ledger_dir = temppath;

        wal_os.open(ledger_dir / "wal", std::ios::binary);

        MONAD_ASSERT(wal_os);
    }

    void TearDown() override
    {
        wal_os.close();
        std::filesystem::remove_all(ledger_dir);
    }
};

TEST_F(BlockEmitterTestFixture, open_empty)
{
    WalEmitter emitter(ledger_dir);
    EXPECT_EQ(emitter.next(), std::nullopt);

    append_entry(MONAD_WAL_PROPOSE, 1);

    auto const output_e = emitter.next();
    ASSERT_TRUE(output_e.has_value());
    EXPECT_EQ(output_e.value().action, MONAD_WAL_PROPOSE);
    EXPECT_EQ(output_e.value().header.round, 1);
}

TEST_F(BlockEmitterTestFixture, replay_from_start)
{
    append_entry(MONAD_WAL_PROPOSE, 1);
    append_entry(MONAD_WAL_FINALIZE, 1);

    WalEmitter emitter(ledger_dir);

    auto const a0 = emitter.next();
    ASSERT_TRUE(a0.has_value());
    EXPECT_EQ(a0.value().action, MONAD_WAL_PROPOSE);
    EXPECT_EQ(a0.value().header.round, 1);

    auto const a1 = emitter.next();
    ASSERT_TRUE(a1.has_value());
    EXPECT_EQ(a1.value().action, MONAD_WAL_FINALIZE);
    EXPECT_EQ(a1.value().header.round, 1);

    // execution is now ahead
    EXPECT_FALSE(emitter.next().has_value());
}

TEST_F(BlockEmitterTestFixture, rewind)
{
    for (uint64_t i = 0; i < 6; ++i) {
        append_entry(MONAD_WAL_PROPOSE, i);
    }

    monad_wal_action const bad_rewind{
        .action = MONAD_WAL_FINALIZE, .id = bytes32_t{70'000}};
    monad_wal_action const good_rewind{
        .action = MONAD_WAL_PROPOSE, .id = bytes32_t{3}};

    WalEmitter emitter(ledger_dir);
    ASSERT_FALSE(emitter.rewind_to(bad_rewind));
    ASSERT_TRUE(emitter.rewind_to(good_rewind));

    for (uint64_t i = 3; i < 6; ++i) {
        auto const action = emitter.next();
        ASSERT_TRUE(action.has_value());
        EXPECT_EQ(action.value().action, MONAD_WAL_PROPOSE);
        EXPECT_EQ(action.value().header.round, i);
    }
}

TEST_F(BlockEmitterTestFixture, open_bad_data)
{
    uint64_t const garbage = std::numeric_limits<uint64_t>::max();
    wal_os.write(reinterpret_cast<char const *>(&garbage), sizeof(garbage));
    wal_os.flush();

    WalEmitter emitter(ledger_dir);
    EXPECT_FALSE(emitter.next().has_value());

    // simulate consensus writing over the bad data with a proper event
    wal_os.seekp(0, std::ios::beg);
    append_entry(MONAD_WAL_PROPOSE, 1);

    auto const action = emitter.next();
    ASSERT_TRUE(action.has_value());
    EXPECT_EQ(action.value().action, MONAD_WAL_PROPOSE);
    EXPECT_EQ(action.value().header.round, 1);
}

TEST_F(BlockEmitterTestFixture, partial_write)
{
    WalEmitter emitter(ledger_dir);
    ASSERT_FALSE(emitter.next().has_value());

    write_dummy_block(1);
    monad_wal_action act{.action = MONAD_WAL_PROPOSE, .id = bytes32_t{1}};
    auto const partial_size = sizeof(monad_wal_action) - 3;

    // write half
    wal_os.write(reinterpret_cast<char *>(&act), partial_size);
    wal_os.flush();

    // no event yet...
    EXPECT_FALSE(emitter.next().has_value());

    // write other half
    wal_os.write(reinterpret_cast<char *>(&act) + partial_size, 3);
    wal_os.flush();
    ASSERT_EQ(wal_os.tellp(), sizeof(monad_wal_action));

    auto const next_action = emitter.next();
    ASSERT_TRUE(next_action.has_value());
    EXPECT_EQ(next_action.value().action, MONAD_WAL_PROPOSE);
    EXPECT_EQ(next_action.value().header.round, 1);
}

TEST(EventEmitter, replay_emulate)
{
    ReplayEmitter emitter(test_resource::correct_block_data_dir);

    auto validate_header_fn = [](MonadConsensusBlockHeader const &header,
                                 uint64_t const n) {
        EXPECT_EQ(header.execution_inputs.number, n);
        EXPECT_EQ(header.round, n);
        EXPECT_EQ(header.parent_round(), n - 1);
        EXPECT_EQ(header.parent_id(), bytes32_t{n - 1});
        ASSERT_EQ(header.delayed_execution_results.size(), 1);
    };

    for (uint64_t i = 1; i <= 2; ++i) {
        auto action = emitter.next();
        ASSERT_TRUE(action.has_value());
        EXPECT_EQ(action.value().action, MONAD_WAL_PROPOSE);
        validate_header_fn(action.value().header, i);

        action = emitter.next();
        ASSERT_TRUE(action.has_value());
        EXPECT_EQ(action.value().action, MONAD_WAL_FINALIZE);
        validate_header_fn(action.value().header, i);
    }
}
