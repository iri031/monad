#include <CLI/CLI.hpp>

#include <category/storage/db_storage.hpp>

#include <filesystem>
using namespace MONAD_STORAGE_NAMESPACE;

int main(int const argc, char const *argv[])
{

    CLI::App cli("Tool for managing MPT databases", "monad_mpt");
    cli.footer(R"(Suitable sources of block storage:

1. Raw partitions on a storage device.
2. The storage device itself.
3. A file on a filing system (use 'truncate -s 1T sparsefile' to create and
set it to the desired size beforehand).

The storage source order must be identical to database creation, as must be
the source type, size and device id, otherwise the database cannot be
opened.
)");

    std::filesystem::path storage_path;
    bool truncate_database = false;

    cli.add_option(
           "--storage",
           storage_path,
           "one or more sources of block storage (must be at least "
           "<chunk_capacity> + 4Kb long).")
        ->required();
    cli.add_flag(
        "--truncate",
        truncate_database,
        "truncates an existing database to empty, efficiently "
        "discarding "
        "all existing storage.");

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }

    if (truncate_database) {
        DbStorage(storage_path, DbStorage::Mode::truncate);
    }
}
