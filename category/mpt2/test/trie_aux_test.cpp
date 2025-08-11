#include "gtest/gtest.h"

#include <category/mpt2/state_machine.hpp>
#include <category/mpt2/test/test_fixtures.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/util.hpp>
#include <category/storage/db_storage.hpp>
#include <category/storage/util.hpp>

#include <filesystem>
#include <memory>

#include "unistd.h"

using namespace MONAD_MPT2_NAMESPACE;
using namespace MONAD_STORAGE_NAMESPACE;
using namespace monad::trie_test;

std::filesystem::path create_temp_file(long size_gb)
{
    std::filesystem::path const filename{
        working_temporary_directory() / "monad_trie_test_XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(-1 != ::ftruncate(fd, size_gb * 1024 * 1024 * 1024));
    ::close(fd);
    return filename;
}

struct UpdateAuxFixture : public ::testing::Test
{
    std::filesystem::path const path;
    DbStorage db_storage;
    UpdateAux aux;
    std::unique_ptr<StateMachine> sm;

    UpdateAuxFixture()
        : path{create_temp_file(8)}
        , db_storage(path, DbStorage::Mode::truncate)
        , aux(db_storage) // using default history
        , sm(std::make_unique<StateMachineAlwaysMerkle>())
    {
    }

    ~UpdateAuxFixture() noexcept
    {
        std::filesystem::remove(path);
    }
};

TEST_F(UpdateAuxFixture, upsert_works)
{
    auto const &kv = fixed_updates::kv;

    {
        WriteTransaction wt(aux);
        UpdateList update_ls;
        Update u1 = make_update(kv[0].first, kv[0].second),
               u2 = make_update(kv[1].first, kv[1].second);
        update_ls.push_front(u1);
        update_ls.push_front(u2);
        auto const root_offset = wt.do_upsert(
            INVALID_OFFSET, *sm, std::move(update_ls), 0, false, true);
        wt.finish(root_offset, 0);
    }

    // aux.db_storage().get
}
