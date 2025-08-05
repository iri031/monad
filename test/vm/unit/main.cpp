#include "test_params.hpp"

#include <CLI/CLI.hpp>
#include <filesystem>
#include <gtest/gtest.h>

int main(int argc, char *argv[])
{
    // Process GoogleTest flags.
    testing::InitGoogleTest(&argc, argv);

    // Then our own flags.
    CLI::App app{"Monad VM unit tests", "vm-unit-tests"};
    app.add_flag(
        "--dump-asm",
        monad::vm::compiler::test::params.dump_asm_on_failure,
        "Save assembly on failure");
    CLI11_PARSE(app, argc, argv);

    return RUN_ALL_TESTS();
}
