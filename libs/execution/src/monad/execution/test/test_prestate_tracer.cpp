#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/trace/prestate_tracer.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/account_state.hpp>

#include <ankerl/unordered_dense.h>
#include <boost/fiber/future/promise.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>

#include <test_resource_data.h>

using namespace monad;
using namespace monad::test;

namespace
{
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto key3 =
        0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
    constexpr auto value1 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
    constexpr auto value3 =
        0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
}

TEST(PrestateTracer, pre_state_to_json)
{
    Account const a{.balance = 1000, .code_hash = A_CODE_HASH, .nonce = 1};
    AccountState as{a};
    as.storage_.emplace(key1, value1);
    as.storage_.emplace(key2, value2);
    as.storage_.emplace(key3, value3);

    PreState prestate;
    prestate.emplace(ADDR_A, as);

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};

    commit_sequential(
        tdb,
        StateDeltas{},
        Code{{A_CODE_HASH, A_CODE_ANALYSIS}},
        BlockHeader{.number = 0});

    BlockState bs(tdb);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "0x0000000000000000000000000000000000000100":{
            "balance":"0x3e8",
            "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
            "nonce":1,
            "storage":{
                "0x00000000000000000000000000000000000000000000000000000000cafebabe":"0x0000000000000000000000000000000000000000000000000000000000000003",
                "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c":"0x0000000000000000000000000000000000000000000000000000000000000007",
                "0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b":"0x000000000000000000000000000000000000000000000000000000000000000a"
            }
        }
        
    })";

    EXPECT_EQ(state_to_json(prestate, s), nlohmann::json::parse(json_str));
}
