#pragma once

#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>

#include <filesystem>
#include <optional>

MONAD_TEST_NAMESPACE_BEGIN

class TransactionTest : public testing::Test
{
private:
    std::filesystem::path const file_;
    std::optional<evmc_revision> const revision_;
    std::string contract_compile_dir_;

public:
    TransactionTest(
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

void register_transaction_tests(
        std::optional<evmc_revision> const &,
        std::string const &contract_dir);

MONAD_TEST_NAMESPACE_END
