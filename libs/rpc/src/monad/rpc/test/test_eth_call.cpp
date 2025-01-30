#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/rpc/eth_call.hpp>

#include <gtest/gtest.h>

#include <vector>

using namespace monad;

namespace
{
    std::vector<uint8_t> to_vec(byte_string const &bs)
    {
        std::vector<uint8_t> v{bs.begin(), bs.end()};
        return v;
    }

    // TODO: consolidate fixtures
    struct EthCallFixture : public ::testing::Test
    {
        std::filesystem::path dbname;
        OnDiskMachine machine;
        mpt::Db db;
        TrieDb tdb;

        EthCallFixture()
            : dbname{[] {
                std::filesystem::path dbname(
                    MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                    "monad_eth_call_test1_XXXXXX");
                int const fd = ::mkstemp((char *)dbname.native().data());
                MONAD_ASSERT(fd != -1);
                MONAD_ASSERT(
                    -1 !=
                    ::ftruncate(
                        fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
                ::close(fd);
                return dbname;
            }()}
            , db{machine,
                 mpt::OnDiskDbConfig{.append = false, .dbname_paths = {dbname}}}
            , tdb{db}
        {
        }

        ~EthCallFixture()
        {
            std::filesystem::remove(dbname);
        }
    };
}

TEST_F(EthCallFixture, simple_success_call)
{
    for (uint64_t i = 0; i < 256; ++i) {
        BlockHeader hdr{.number = i};
        tdb.commit({}, {}, hdr);
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 256};

    tdb.set_block_and_round(header.number - 1);
    tdb.commit({}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    monad_state_override_set state_override;

    auto const result = eth_call(
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx,
        rlp_header,
        rlp_sender,
        256u,
        dbname,
        state_override);

    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);
}

TEST_F(EthCallFixture, failed_to_read)
{
    // missing 256 previous blocks
    load_header(db, BlockHeader{.number = 1199});
    for (uint64_t i = 1200; i < 1256; ++i) {
        tdb.set_block_and_round(i - 1);
        tdb.commit({}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 1256};

    tdb.set_block_and_round(header.number - 1);
    tdb.commit({}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    monad_state_override_set state_override;

    auto const result = eth_call(
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx,
        rlp_header,
        rlp_sender,
        1256u,
        dbname,
        state_override);
    EXPECT_EQ(result.status_code, EVMC_REJECTED);
}

TEST_F(EthCallFixture, contract_deployment_success)
{
    for (uint64_t i = 0; i < 256; ++i) {
        BlockHeader hdr{.number = i};
        tdb.commit({}, {}, hdr);
    }

    static constexpr auto from = Address{};

    std::string tx_data =
        "0x604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffff"
        "ffffffffffffffffffffffffe03601600081602082378035828234f580151560395781"
        "82fd5b8082525050506014600cf3";

    Transaction tx{.gas_limit = 100000u, .data = from_hex(tx_data)};
    BlockHeader header{.number = 256};

    tdb.set_block_and_round(header.number - 1);
    tdb.commit({}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    monad_state_override_set state_override;

    auto const result = eth_call(
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx,
        rlp_header,
        rlp_sender,
        256u,
        dbname,
        state_override);

    std::string deployed_code =
        "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe036"
        "01600081602082378035828234f58015156039578182fd5b8082525050506014600cf"
        "3";
    byte_string deployed_code_bytes = from_hex(deployed_code);

    std::vector<uint8_t> deployed_code_vec = {
        deployed_code_bytes.data(),
        deployed_code_bytes.data() + deployed_code_bytes.size()};

    EXPECT_TRUE(result.status_code == EVMC_SUCCESS);
    EXPECT_EQ(result.output_data, deployed_code_vec);
}
