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

    monad::byte_string root_hash(Node *const root)
    {
        if (root) {
            monad::byte_string data(32, 0);
            auto const len = this->sm->get_compute().compute(data.data(), root);
            if (len < KECCAK256_SIZE) {
                keccak256(data.data(), len, data.data());
            }
            return data;
        }
        return empty_trie_hash;
    }
};

TEST_F(UpdateAuxFixture, upsert_works)
{
    auto const &kv = fixed_updates::kv;

    chunk_offset_t root_offset = INVALID_OFFSET;
    uint64_t version = 0;
    { // version 0
        WriteTransaction wt(aux);
        UpdateList update_ls;
        Update u1 = make_update(kv[0].first, kv[0].second),
               u2 = make_update(kv[1].first, kv[1].second);
        update_ls.push_front(u1);
        update_ls.push_front(u2);
        root_offset = wt.do_upsert(
            INVALID_OFFSET, *sm, std::move(update_ls), version, false, true);
        wt.finish(root_offset, version);
    }

    EXPECT_EQ(
        aux.db_storage().get_root_offset_at_version(version), root_offset);
    NodeCursor const root_cursor{*aux.parse_node(root_offset)};
    // find
    auto const [cursor, res] = find(aux, root_cursor, kv[0].first, version);
    EXPECT_EQ(res, find_result::success);
    EXPECT_EQ(cursor.node->value(), kv[0].second);
    // root hash
    EXPECT_EQ(
        this->root_hash(root_cursor.node),
        0x05a697d6698c55ee3e4d472c4907bca2184648bcfdd0e023e7ff7089dc984e7e_hex);

    ++version;
    { // version 1
        WriteTransaction wt(aux);
        UpdateList update_ls;
        Update u1 = make_update(kv[2].first, kv[2].second),
               u2 = make_update(kv[3].first, kv[3].second);
        update_ls.push_front(u1);
        update_ls.push_front(u2);
        root_offset = wt.do_upsert(
            root_offset, *sm, std::move(update_ls), version, false, true);
        wt.finish(root_offset, version);
    }
    // root hash
    NodeCursor const root_cursor2{*aux.parse_node(root_offset)};
    EXPECT_EQ(
        this->root_hash(root_cursor2.node),
        0x22f3b7fc4b987d8327ec4525baf4cb35087a75d9250a8a3be45881dd889027ad_hex);
}
