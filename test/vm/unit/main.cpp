#include "test_params.hpp"

#include <CLI/CLI.hpp>
#include <filesystem>
#include <gtest/gtest.h>

int main(int argc, char *argv[])
{
    // Process GoogleTest flags.
    testing::InitGoogleTest(&argc, argv);

    return RUN_ALL_TESTS();
}
