#include <category/mpt2/db.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/mpt2/db_error.hpp>
#include <category/mpt2/nibbles_view.hpp>
#include <category/mpt2/node.hpp>
#include <category/mpt2/node_cursor.hpp>
#include <category/mpt2/ondisk_db_config.hpp>
#include <category/mpt2/traverse.hpp>
#include <category/mpt2/trie.hpp>
#include <category/mpt2/update.hpp>
#include <category/mpt2/util.hpp>

#include <quill/Quill.h>

#include <atomic>
#include <cerrno>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <stdexcept>
#include <system_error>
#include <utility>
#include <vector>

#include <fcntl.h>
#include <linux/fs.h>
#include <unistd.h>

MONAD_MPT2_NAMESPACE_BEGIN

DbError find_result_to_db_error(find_result const result) noexcept
{
    switch (result) {
    case find_result::key_mismatch_failure:
    case find_result::branch_not_exist_failure:
    case find_result::key_ends_earlier_than_node_failure:
        return DbError::key_not_found;
    case find_result::root_node_is_null_failure:
    case find_result::version_no_longer_exist:
        return DbError::version_no_longer_exist;
    case find_result::unknown:
        return DbError::unknown;
    default:
        MONAD_ASSERT_PRINTF(
            false, "Unexpected find result: %d", static_cast<int>(result));
        return DbError::unknown;
    }
}

// RWDb
Db::Db(StateMachine &sm, OnDiskDbConfig const &config)
    : sm_(sm)
    , storage_([&] {
        if (config.dbname_path.empty()) {
            auto len = config.file_size_db * 1024 * 1024 * 1024 + 24576;
            return storage::DbStorage(storage::use_anonymous_inode_tag{}, len);
        }
        return storage::DbStorage(
            config.dbname_path,
            config.append ? storage::DbStorage::Mode::open_existing
                          : storage::DbStorage::Mode::create_if_needed);
    }())
    , aux_(storage_, config.fixed_history_length)
{
}

NodeCursor Db::load_root_for_version(uint64_t const version) const
{
    auto root_offset = version == wip_version_
                           ? wip_root_offset_
                           : aux_.get_root_offset_at_version(version);
    if (root_offset == INVALID_OFFSET) {
        return NodeCursor{};
    }
    auto *node = aux_.parse_node(root_offset);
    if (node == nullptr) {
        return NodeCursor{};
    }
    return NodeCursor{*node};
}

OwningNodeCursor Db::load_root_for_version_weak(uint64_t const version) const
{
    auto root_offset = aux_.get_root_offset_at_version(version);
    if (root_offset == INVALID_OFFSET) {
        return OwningNodeCursor{};
    }
    auto node = aux_.parse_node_weak(root_offset, version);
    return OwningNodeCursor{std::move(node)};
}

Result<NodeCursor> Db::find(
    NodeCursor const start, NibblesView const key, uint64_t const version) const
{
    if (!start.is_valid()) {
        return DbError::version_no_longer_exist;
    }
    if (key.empty()) {
        return start;
    }
    auto [cursor, result] = mpt2::find(aux_, start, key, version);
    if (result != find_result::success) {
        return find_result_to_db_error(result);
    }
    MONAD_DEBUG_ASSERT(cursor.is_valid());
    MONAD_DEBUG_ASSERT(cursor.node->has_value());
    return cursor;
}

Result<NodeCursor> Db::find(NibblesView key, uint64_t version) const
{
    return find(load_root_for_version(version), key, version);
}

Result<OwningNodeCursor> Db::find_weak(NibblesView key, uint64_t version) const
{
    auto [cursor, result] = mpt2::find_weak(
        aux_, load_root_for_version_weak(version), key, version);
    if (result != find_result::success) {
        return find_result_to_db_error(result);
    }
    MONAD_DEBUG_ASSERT(cursor.is_valid());
    MONAD_DEBUG_ASSERT(cursor.node->has_value());
    return std::move(cursor);
}

Result<byte_string_view>
Db::get(NibblesView const key, uint64_t const version) const
{
    auto res = find(key, version);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    if (!res.value().node->has_value()) {
        return DbError::key_not_found;
    }
    return res.value().node->value();
}

Result<byte_string_view> Db::get_data(
    NodeCursor root, NibblesView const key, uint64_t const version) const
{
    auto res = find(root, key, version);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);
    return res.value().node->data();
}

Result<byte_string_view>
Db::get_data(NibblesView const key, uint64_t const version) const
{
    auto res = find(key, version);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);
    return res.value().node->data();
}

void Db::start_transaction(uint64_t const version)
{
    MONAD_ASSERT(
        wt_ == nullptr,
        "Transaction already started, cannot start two transactions at the "
        "same time");
    wt_ = std::make_unique<WriteTransaction>(aux_);
    wip_root_offset_ = aux_.get_root_offset_at_version(version);
    wip_version_ = version;
}

void Db::finish_transaction(uint64_t const version)
{
    MONAD_ASSERT(wt_, "No transaction started, call start_transaction first");
    wt_->finish(wip_root_offset_, version);
    wt_.reset();
    wip_root_offset_ = INVALID_OFFSET;
    wip_version_ = INVALID_BLOCK_NUM;
}

void Db::upsert(
    UpdateList list, uint64_t const version, bool const enable_compaction,
    bool const can_write_to_fast)
{
    MONAD_ASSERT(
        wt_, "No db transaction started, call start_transaction() first");
    wip_root_offset_ = wt_->do_upsert(
        wip_root_offset_,
        sm_,
        std::move(list),
        version,
        enable_compaction,
        can_write_to_fast);
    wip_version_ = version;
}

void Db::copy_trie(
    uint64_t const src_version, NibblesView const src_prefix,
    uint64_t const dest_version, NibblesView const dest_prefix)
{
    MONAD_ASSERT(
        wt_, "No db transaction started, call start_transaction() first");
    wip_root_offset_ = wt_->copy_trie(
        aux_.get_root_offset_at_version(src_version),
        src_prefix,
        dest_version,
        dest_prefix);
    wip_version_ = dest_version;
}

void Db::update_finalized_version(uint64_t version)
{
    aux_.set_latest_finalized_version(version);
}

void Db::update_verified_version(uint64_t version)
{
    aux_.set_latest_verified_version(version);
}

void Db::update_voted_metadata(uint64_t version, bytes32_t const &block_id)
{
    aux_.set_latest_voted(version, block_id);
}

uint64_t Db::get_latest_finalized_version() const
{
    return aux_.get_latest_finalized_version();
}

uint64_t Db::get_latest_verified_version() const
{
    return aux_.get_latest_verified_version();
}

bytes32_t Db::get_latest_voted_block_id() const
{
    return aux_.get_latest_voted_block_id();
}

uint64_t Db::get_latest_voted_version() const
{
    return aux_.get_latest_voted_version();
}

uint64_t Db::get_latest_version() const
{
    return aux_.db_history_max_version();
}

uint64_t Db::get_earliest_version() const
{
    return aux_.db_history_min_valid_version();
}

uint64_t Db::get_history_length() const
{
    return aux_.version_history_length();
}

bool Db::traverse(NodeCursor root, TraverseMachine &machine, uint64_t block_id)
{
    return preorder_traverse_blocking(aux_, *root.node, machine, block_id);
}

RODb::RODb(std::filesystem::path const db_path)
    : storage_(db_path, storage::DbStorage::Mode::open_existing)
    , aux_(storage_, std::nullopt)
{
}

OwningNodeCursor RODb::load_root_for_version(uint64_t version) const
{
    auto root_offset = aux_.get_root_offset_at_version(version);
    if (root_offset == INVALID_OFFSET) {
        return OwningNodeCursor{};
    }
    auto node = aux_.parse_node_weak(root_offset, version);
    return OwningNodeCursor{std::move(node)};
}

Result<OwningNodeCursor> RODb::find(NibblesView key, uint64_t version) const
{
    auto [cursor, result] =
        mpt2::find_weak(aux_, load_root_for_version(version), key, version);
    if (result != find_result::success) {
        return find_result_to_db_error(result);
    }
    MONAD_DEBUG_ASSERT(cursor.is_valid());
    MONAD_DEBUG_ASSERT(cursor.node->has_value());
    return std::move(cursor);
}

Result<OwningNodeCursor>
RODb::find(OwningNodeCursor root, NibblesView key, uint64_t version) const
{
    auto [cursor, result] =
        mpt2::find_weak(aux_, std::move(root), key, version);
    if (result != find_result::success) {
        return find_result_to_db_error(result);
    }
    MONAD_DEBUG_ASSERT(cursor.is_valid());
    MONAD_DEBUG_ASSERT(cursor.node->has_value());
    return std::move(cursor);
}

Result<byte_string_view>
RODb::get(NibblesView const key, uint64_t const version) const
{
    auto res = find(key, version);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    if (!res.value().node->has_value()) {
        return DbError::key_not_found;
    }
    return res.value().node->value();
}

Result<byte_string_view> RODb::get_data(
    OwningNodeCursor root, NibblesView const key, uint64_t const version) const
{
    auto res = find(std::move(root), key, version);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);
    return res.value().node->data();
}

Result<byte_string_view>
RODb::get_data(NibblesView const key, uint64_t const version) const
{
    auto res = find(key, version);
    if (!res.has_value()) {
        return DbError(res.error().value());
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);
    return res.value().node->data();
}

bool RODb::traverse(
    OwningNodeCursor const &root, TraverseMachine &machine, uint64_t block_id)
{
    return preorder_traverse_blocking(aux_, *root.node, machine, block_id);
}

uint64_t RODb::get_earliest_version() const
{
    return aux_.db_history_min_valid_version();
}

uint64_t RODb::get_latest_version() const
{
    return aux_.db_history_max_version();
}

uint64_t RODb::get_latest_finalized_version() const
{
    return aux_.get_latest_finalized_version();
}

uint64_t RODb::get_latest_verified_version() const
{
    return aux_.get_latest_verified_version();
}

uint64_t RODb::get_history_length() const
{
    return aux_.version_history_length();
}

MONAD_MPT2_NAMESPACE_END
