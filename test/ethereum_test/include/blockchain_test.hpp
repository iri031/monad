#pragma once

#include <ethereum_test.hpp>

#include <monad/config.hpp>
#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json_fwd.hpp>

#include <filesystem>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Receipt;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

class BlockchainTest : public testing::Test
{
    static fiber::PriorityPool *pool_;

    std::filesystem::path const file_;
    std::optional<evmc_revision> const revision_;
    std::string contract_compile_dir_;

    template <evmc_revision rev>
    static Result<std::vector<Receipt>>
    execute(Block &, test::db_t &, BlockHashBuffer const &);

    static Result<std::vector<Receipt>> execute_dispatch(
        evmc_revision, Block &, test::db_t &, BlockHashBuffer const &);

    static void
    validate_post_state(nlohmann::json const &json, nlohmann::json const &db);

public:
    static void SetUpTestSuite();
    static void TearDownTestSuite();

    BlockchainTest(
        std::filesystem::path const &file,
        std::optional<evmc_revision> const &revision,
        std::string const &contract_dir) noexcept
        : file_{file}
        , revision_{revision}
        , contract_compile_dir_{contract_dir}
    {
    }

    void TestBody() override;
};

void register_blockchain_tests(std::optional<evmc_revision> const &,
        std::string const &contract_dir, bool enable_slow_tests);

MONAD_TEST_NAMESPACE_END
