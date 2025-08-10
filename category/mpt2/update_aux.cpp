#include <category/mpt2/config.hpp>
#include <category/mpt2/trie.hpp>

#include <cstdint>
#include <option>

MONAD_MPT2_NAMESPACE_BEGIN

UpdateAux::UpdateAux(
    DbStorage &db_storage, std::optional<uint64_t> const history_len)
    : db_storage_(db_storage)
    , enable_dynamic_history_length_(!history_len.has_value())
{
    if (history_len.has_value() && !is_read_only()) {
        // reset history length
        if (history_len < version_history_length() &&
            history_len <= db_history_max_version()) {
            // we invalidate earlier blocks that fall outside of the
            // history window when shortening history length
            erase_versions_up_to_and_including(
                db_history_max_version() - *history_len); // TODO: impl this
        }
        update_history_length_metadata(*history_len);
    }

    // init node writers
    node_writer_offset_fast =
        db_storage_.db_metadata()->db_offsets.start_of_wip_offset_fast;
    node_writer_offset_slow =
        db_storage_.db_metadata()->db_offsets.start_of_wip_offset_slow;

    // init last block end offsets
    last_block_end_offset_fast_ = compact_virtual_chunk_offset_t{
        physical_to_virtual(node_writer_fast->sender().offset())};
    last_block_end_offset_slow_ = compact_virtual_chunk_offset_t{
        physical_to_virtual(node_writer_slow->sender().offset())};
}

Node *UpdateAux::parse_node(chunk_offset_t const offset) const noexcept
{
    if (offset == INVALID_OFFSET) {
        return nullptr;
    }
    return parse_node(db_storage_.get_data(offset), offset);
}

chunk_offset_t
UpdateAux::write_node_to_disk(Node::UniquePtr node, bool const to_fast_list)
{
    // Append node to the dedicated chunk list
    // If node size fit the remaining bytes, append to the current chunk,
    // otherwise start a new chunk and write there. Node max size guarantees it
    // can always fit in a chunk of default capacity
    auto &node_writer_offset =
        to_fast_list ? node_writer_offset_fast : node_writer_offset_slow;
    auto const chunk_bytes_written =
        db_storage_.chunk_bytes_used(node_writer_offset.id);
    MONAD_ASSERT_PRINTF(
        chunk_bytes_written == node_writer_offset.offset,
        "where we are appending %u is not where we are supposed to be "
        "appending %llu, check if there are multiple writers writes to db "
        "concurrently. Chunk id is %u",
        node_writer_offset.offset,
        chunk_bytes_written,
        node_writer_offset.id);

    auto const chunk_remaining_bytes =
        db_storage_.chunk_capacity() - node_writer_offset.offset;
    auto const bytes_to_append = node->get_disk_size();
    if (bytes_to_append > chunk_remaining_bytes) {
        // allocate a new chunk from free list to the specified list and update
        // node_writer_offset to the start of the new chunk
        db_metadata_t::chunk_info_t const *ci =
            db_storage_.db_metadata().main->free_list_end();
        MONAD_ASSERT_PRINTF(
            ci != nullptr, "disk is full, we are out of free blocks");
        uint32_t const idx = ci->index(db_storage_.db_metadata().main);
        db_storage.remove(idx);
        db_storage.append(
            to_fast_list ? DbStorage::chunk_list::fast
                         : DbStorage::chunk_list::slow);
        node_writer_offset.id = idx & 0xfffffU;
        node_writer_offset.offset = 0;
    }
    serialize_node(db_storage_.get_data(node_writer_offset), *node);
    db_storage_.advance_chunk_bytes_used(
        node_writer_offset.id, bytes_to_append);
    return node_writer_offset;
}

void UpdateAux::finalize_transaction(
    chunk_offset_t const root_offset, uint64_t const version)
{
    // update root offset in ring buffer
    // update writer offset trackers
    db_storage_.advance_db_offsets_to(
        node_writer_offset_fast, node_writer_offset_slow);
    auto const max_version_in_db = db_history_max_version();
    if (MONAD_UNLIKELY(max_version_in_db == INVALID_BLOCK_NUM)) {
        fast_forward_next_version(version);
        append_root_offset(offset_written_to);
        MONAD_ASSERT(db_history_range_lower_bound() == version);
    }
    else if (version <= max_version_in_db) {
        MONAD_ASSERT(
            version >= ((max_version_in_db >= version_history_length())
                            ? max_version_in_db - version_history_length() + 1
                            : 0));
        auto const prev_lower_bound = db_history_range_lower_bound();
        update_root_offset(version, offset_written_to);
        MONAD_ASSERT(
            db_history_range_lower_bound() ==
            std::min(version, prev_lower_bound));
    }
    else {
        MONAD_ASSERT(version == max_version_in_db + 1);
        append_root_offset(offset_written_to);
    }

    write_mutex_.unlock();
}

chunk_offset_t UpdateAux::db_upsert(
    chunk_offset_t const root_offset, StateMachine &sm, UpdateList &&updates,
    uint64_t const version, bool const compaction, bool const can_write_to_fast)
{
    // TODO: update compaction offsets
    // TODO: dynamically adjust history length
    // TODO: prune versions that are going to fall out of history window

    return upsert(*this, version, sm, root_offset, std::move(updates));
}

MONAD_MPT2_NAMESPACE_END
