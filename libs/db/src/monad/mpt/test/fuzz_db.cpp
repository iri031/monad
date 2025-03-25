#include "test_fixtures_base.hpp"
#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>

#include <quill/Quill.h>

#include <cstdint>
#include <deque>
#include <filesystem>
#include <memory>

namespace
{
    std::filesystem::path create_temp_file()
    {
        std::filesystem::path const filename{
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_fuzz_db_XXXXXX"};
        int const fd = ::mkstemp((char *)filename.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(-1 != ::ftruncate(fd, 4ul * 1024 * 1024 * 1024));
        ::close(fd);
        return filename;
    }
}

extern "C" int
LLVMFuzzerTestOneInput(uint8_t const *const data, size_t const size)
{
    using namespace monad;
    using namespace monad::mpt;

    if (size < 1000) {
        return -1;
    }

    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Info);

    auto const path = create_temp_file();
    test::StateMachineAlwaysMerkle machine;
    std::unique_ptr<Db> db = std::make_unique<Db>(
        machine,
        OnDiskDbConfig{
            .append = false,
            .compaction = true,
            .rd_buffers = 8192,
            .wr_buffers = 32,
            .uring_entries = 128,
            .dbname_paths = {path}});

    std::vector<Nibbles> nibbles;
    for (size_t i = 0; i < 2'000'000; ++i) {
        byte_string const n{
            reinterpret_cast<unsigned char const *>(&i), sizeof(i)};
        nibbles.emplace_back(keccak256(byte_string_view{n}));
    }

    std::deque<Update> updates;
    UpdateList update_list;
    byte_string const val(1024, 'A');
    for (size_t i = 0; i < 1'000'000; ++i) {
        update_list.push_front(updates.emplace_back(Update{
            .key = NibblesView{nibbles.at(i)},
            .value = byte_string_view{val},
            .next = {}}));
    }
    db->upsert(std::move(update_list), 0);
    db->update_finalized_block(0);

    auto const upsert = [&db, &nibbles, &updates, &val, &update_list](
                            uint8_t const byte, uint64_t const version) {
        updates.clear();
        update_list.clear();
        for (uint8_t i = 0; i < byte; ++i) {
            update_list.push_front(updates.emplace_back(Update{
                .key = NibblesView{nibbles.at(i)},
                .value = byte_string_view{val},
                .next = {}}));
        }
        db->upsert(std::move(update_list), version);
    };

    db->update_finalized_block(0);

    std::span<uint8_t const> raw{data, size};
    for (uint8_t const byte : raw) {
        uint64_t const earliest = db->get_earliest_block_id();
        uint64_t const latest = db->get_latest_block_id();
        MONAD_ASSERT(
            earliest != INVALID_BLOCK_ID && latest != INVALID_BLOCK_ID);

        switch (byte % 4) {
        case 0: { // update existing
            uint64_t const version =
                std::max(earliest, latest - std::min(latest, (size_t)byte));
            LOG_INFO("Update existing version={}", version);
            upsert(byte, version);
        } break;
            // case 1: { // rewind
            //     LOG_INFO("rewind_to_latest_finalized");
            //     db = std::make_unique<Db>(
            //         machine,
            //         OnDiskDbConfig{
            //             .append = true,
            //             .compaction = true,
            //             .rewind_to_latest_finalized = true,
            //             .rd_buffers = 8192,
            //             .wr_buffers = 32,
            //             .uring_entries = 128,
            //             .dbname_paths = {path}});
            // } break;
        case 2: { // move_trie_forward
            LOG_INFO(
                "move_trie_version_forward from {} to {}",
                latest,
                latest + byte);
            db->move_trie_version_forward(latest, latest + byte);
            db->update_finalized_block(latest + byte);
        } break;
        default: {
            LOG_INFO(
                "Insert new version={} finalized={}", latest + 1, byte % 2);
            upsert(byte, latest + 1);
            if (byte % 2) {
                db->update_finalized_block(latest + 1);
            }
        } break;
        }
    }

    std::filesystem::remove(path);

    return 0;
}
