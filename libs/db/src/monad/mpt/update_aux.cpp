#include <monad/async/config.hpp>
#include <monad/async/detail/start_lifetime_as_polyfill.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/detail/unsigned_20.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <random>
#include <span>
#include <stdexcept>
#include <thread>
#include <utility>
#include <vector>

#include <sys/mman.h>
#include <unistd.h>

MONAD_MPT_NAMESPACE_BEGIN

using namespace MONAD_ASYNC_NAMESPACE;

void write_operation_io_receiver::set_value(
    MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
    MONAD_ASYNC_NAMESPACE::write_no_owning_buffer_sender::result_type res)
{
    MONAD_ASSERT(res);
    if (this->offset_to_remove_until == INVALID_OFFSET) {
        // nothing to release
        return;
    }
    auto &buffered_writes =
        is_fast ? aux->write_back_buffer_fast : aux->write_back_buffer_slow;

    while (buffered_writes.items.front().offset !=
           this->offset_to_remove_until) {
        buffered_writes.pop();
    }
    MONAD_ASSERT(!buffered_writes.items.empty());
    auto const &first_item = buffered_writes.items.front();
    MONAD_DEBUG_ASSERT(first_item.offset == this->offset_to_remove_until);
    MONAD_ASSERT(first_item.buffer.data() == res.assume_value().get().data());
    buffered_writes.pop();
}

// Define to avoid randomisation of free list chunks on pool creation
// This can be useful to discover bugs in code which assume chunks are
// consecutive
// #define MONAD_MPT_INITIALIZE_POOL_WITH_CONSECUTIVE_CHUNKS 1

virtual_chunk_offset_t
UpdateAuxImpl::physical_to_virtual(chunk_offset_t const offset) const noexcept
{
    MONAD_ASSERT(offset.id < io->chunk_count());
    auto const *ci = db_metadata_[0]->at(offset.id);
    // should never invoke a translation for offset in free list
    MONAD_DEBUG_ASSERT(ci->in_fast_list || ci->in_slow_list);
    return {
        uint32_t(ci->insertion_count()),
        offset.offset,
        ci->in_fast_list,
        offset.spare & virtual_chunk_offset_t::max_spare};
}

std::pair<UpdateAuxImpl::chunk_list, detail::unsigned_20>
UpdateAuxImpl::chunk_list_and_age(uint32_t const idx) const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const *ci = db_metadata_[0]->at(idx);
    std::pair<chunk_list, detail::unsigned_20> ret(
        chunk_list::free, ci->insertion_count());
    if (ci->in_fast_list) {
        ret.first = chunk_list::fast;
        ret.second -= db_metadata_[0]->fast_list_begin()->insertion_count();
    }
    else if (ci->in_slow_list) {
        ret.first = chunk_list::slow;
        ret.second -= db_metadata_[0]->slow_list_begin()->insertion_count();
    }
    else {
        ret.second -= db_metadata_[0]->free_list_begin()->insertion_count();
    }
    return ret;
}

void UpdateAuxImpl::append(chunk_list const list, uint32_t const idx) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        switch (list) {
        case chunk_list::free:
            m->append_(m->free_list, m->at_(idx));
            break;
        case chunk_list::fast:
            m->append_(m->fast_list, m->at_(idx));
            break;
        case chunk_list::slow:
            m->append_(m->slow_list, m->at_(idx));
            break;
        }
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
    if (list == chunk_list::free) {
        auto chunk = io->storage_pool().chunk(storage_pool::seq, idx);
        auto capacity = chunk->capacity();
        MONAD_DEBUG_ASSERT(chunk->size() == 0);
        db_metadata_[0]->free_capacity_add_(capacity);
        db_metadata_[1]->free_capacity_add_(capacity);
    }
}

void UpdateAuxImpl::remove(uint32_t const idx) noexcept
{
    MONAD_ASSERT(is_on_disk());
    bool const is_free_list =
        (!db_metadata_[0]->at_(idx)->in_fast_list &&
         !db_metadata_[0]->at_(idx)->in_slow_list);
    auto do_ = [&](detail::db_metadata *m) { m->remove_(m->at_(idx)); };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
    if (is_free_list) {
        auto chunk = io->storage_pool().chunk(storage_pool::seq, idx);
        auto capacity = chunk->capacity();
        MONAD_DEBUG_ASSERT(chunk->size() == 0);
        db_metadata_[0]->free_capacity_sub_(capacity);
        db_metadata_[1]->free_capacity_sub_(capacity);
    }
}

void UpdateAuxImpl::advance_db_offsets_to(
    chunk_offset_t const fast_offset, chunk_offset_t const slow_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    // To detect bugs in replacing fast/slow node writer to the wrong chunk
    // list
    MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
    MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);
    auto do_ = [&](detail::db_metadata *m) {
        m->advance_db_offsets_to_(detail::db_metadata::db_offsets_info_t{
            fast_offset,
            slow_offset,
            this->compact_offset_fast,
            this->compact_offset_slow,
            this->compact_offset_range_fast_,
            this->compact_offset_range_slow_});
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::append_root_offset(
    chunk_offset_t const root_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->append_root_offset_(root_offset);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::update_root_offset(
    size_t const i, chunk_offset_t const root_offset) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->update_root_offset_(i, root_offset);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::fast_forward_next_version(uint64_t const version) noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->fast_forward_next_version_(version);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::update_slow_fast_ratio_metadata() noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const ratio = (float)num_chunks(chunk_list::slow) /
                       (float)num_chunks(chunk_list::fast);
    auto do_ = [&](detail::db_metadata *m) {
        m->update_slow_fast_ratio_(ratio);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::update_history_length_metadata(
    uint64_t const history_len) noexcept
{
    std::cout << "Update db history length to " << history_len << std::endl;
    MONAD_ASSERT(is_on_disk());
    auto do_ = [&](detail::db_metadata *m) {
        m->set_history_length_(history_len);
    };
    do_(db_metadata_[0]);
    do_(db_metadata_[1]);
}

void UpdateAuxImpl::rewind_to_match_offsets()
{
    MONAD_ASSERT(is_on_disk());
    // Free all chunks after fast_offset.id
    auto const fast_offset = db_metadata()->db_offsets.start_of_wip_offset_fast;
    MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
    auto const slow_offset = db_metadata()->db_offsets.start_of_wip_offset_slow;
    MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);

    auto const *ci = db_metadata_[0]->at(fast_offset.id);
    while (ci != db_metadata_[0]->fast_list_end()) {
        auto const idx = db_metadata_[0]->fast_list.end;
        remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx)->destroy_contents();
        append(chunk_list::free, idx);
    }
    auto fast_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, fast_offset.id);
    MONAD_ASSERT(fast_offset_chunk->try_trim_contents(fast_offset.offset));

    // Same for slow list
    auto const *slow_ci = db_metadata_[0]->at(slow_offset.id);
    while (slow_ci != db_metadata_[0]->slow_list_end()) {
        auto const idx = db_metadata_[0]->slow_list.end;
        remove(idx);
        io->storage_pool().chunk(storage_pool::seq, idx)->destroy_contents();
        append(chunk_list::free, idx);
    }
    auto slow_offset_chunk =
        io->storage_pool().chunk(storage_pool::seq, slow_offset.id);
    MONAD_ASSERT(slow_offset_chunk->try_trim_contents(slow_offset.offset));

    // Reset node_writers offset to the same offsets in db_metadata
    reset_node_writers();
}

UpdateAuxImpl::~UpdateAuxImpl()
{
    if (io != nullptr) {
        unset_io();
    }
}

#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
void UpdateAuxImpl::set_io(AsyncIO *io_, uint64_t const history_len)
{
    io = io_;
    auto const chunk_count = io->chunk_count();
    MONAD_ASSERT(chunk_count >= 3);
    auto const map_size =
        sizeof(detail::db_metadata) +
        chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    auto cnv_chunk = io->storage_pool().activate_chunk(storage_pool::cnv, 0);
    auto fdr = cnv_chunk->read_fd();
    auto fdw = cnv_chunk->write_fd(0);
    /* If writable, can map maps writable. If read only but allowing
    dirty, maps are made copy-on-write so writes go into RAM and don't
    affect the original. This lets us heal any metadata and make forward
    progress.
    */
    bool const can_write_to_map =
        (!io->storage_pool().is_read_only() ||
         io->storage_pool().is_read_only_allow_dirty());
    auto &fd = can_write_to_map ? fdw : fdr;
    auto const prot = can_write_to_map ? (PROT_READ | PROT_WRITE) : (PROT_READ);
    auto const mapflags = io->storage_pool().is_read_only_allow_dirty()
                              ? MAP_PRIVATE
                              : MAP_SHARED;
    db_metadata_[0] = start_lifetime_as<detail::db_metadata>(
        ::mmap(nullptr, map_size, prot, mapflags, fd.first, off_t(fdr.second)));
    MONAD_ASSERT(db_metadata_[0] != MAP_FAILED);
    db_metadata_[1] = start_lifetime_as<detail::db_metadata>(::mmap(
        nullptr,
        map_size,
        prot,
        mapflags,
        fd.first,
        off_t(fdr.second + cnv_chunk->capacity() / 2)));
    MONAD_ASSERT(db_metadata_[1] != MAP_FAILED);
    /* If on a storage which ignores TRIM, and the user just truncated
    an existing triedb, all the magics will be valid but the pool has
    been reset. Solve this by detecting when a pool has just been truncated
    and ensure all triedb structures are also reset.
    */
    if (io_->storage_pool().is_newly_truncated()) {
        memset(db_metadata_[0]->magic, 0, sizeof(db_metadata_[0]->magic));
        memset(db_metadata_[1]->magic, 0, sizeof(db_metadata_[1]->magic));
    }
    /* If the front copy vanished for some reason ... this can happen
    if something or someone zaps the front bytes of the partition.
    */
    if (0 != memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (0 == memcmp(
                     db_metadata_[1]->magic,
                     detail::db_metadata::MAGIC,
                     detail::db_metadata::MAGIC_STRING_LEN)) {
            if (can_write_to_map) {
                // Overwrite the front copy with the backup copy
                db_copy(db_metadata_[0], db_metadata_[1], map_size);
            }
            else {
                // We don't have writable maps, so can't forward progress
                throw std::runtime_error("First copy of metadata corrupted, "
                                         "but not opened for healing");
            }
        }
    }

    constexpr unsigned magic_prefix_len =
        detail::db_metadata::MAGIC_STRING_LEN - 1;
    if (0 == memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 magic_prefix_len) &&
        db_metadata_[0]->magic[magic_prefix_len] !=
            detail::db_metadata::MAGIC[magic_prefix_len]) {
        std::stringstream ss;
        ss << "DB was generated with version " << db_metadata_[0]->magic
           << ". The current code base is on version "
           << monad::mpt::detail::db_metadata::MAGIC
           << ". Please regenerate with the new DB version.";
        throw std::runtime_error(ss.str());
    }
    // Replace any dirty copy with the non-dirty copy
    if (0 == memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN) &&
        0 == memcmp(
                 db_metadata_[1]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (can_write_to_map) {
            // Replace the dirty copy with the non-dirty copy
            if (db_metadata_[0]->is_dirty().load(std::memory_order_acquire)) {
                db_copy(db_metadata_[0], db_metadata_[1], map_size);
            }
            else if (db_metadata_[1]->is_dirty().load(
                         std::memory_order_acquire)) {
                db_copy(db_metadata_[1], db_metadata_[0], map_size);
            }
        }
        else {
            if (db_metadata_[0]->is_dirty().load(std::memory_order_acquire) ||
                db_metadata_[1]->is_dirty().load(std::memory_order_acquire)) {
                on_read_only_init_with_dirty_bit();

                // Wait a bit to see if they clear before complaining
                bool dirty;
                auto const begin = std::chrono::steady_clock::now();
                do {
                    dirty = db_metadata_[0]->is_dirty().load(
                                std::memory_order_acquire) ||
                            db_metadata_[1]->is_dirty().load(
                                std::memory_order_acquire);
                    std::this_thread::yield();
                }
                while (dirty && (std::chrono::steady_clock::now() - begin <
                                 std::chrono::seconds(1)));

                /* If after one second a dirty bit remains set, and we don't
                have writable maps, can't forward progress.
                */
                if (dirty) {
                    throw std::runtime_error("DB metadata was closed dirty, "
                                             "but not opened for healing");
                }
            }
        }
    }
    if (0 != memcmp(
                 db_metadata_[0]->magic,
                 detail::db_metadata::MAGIC,
                 detail::db_metadata::MAGIC_STRING_LEN)) {
        if (!can_write_to_map) {
            // We don't have writable maps, so can't forward progress
            throw std::runtime_error(
                "Neither copy of the DB metadata is valid, and not opened for "
                "writing so stopping now.");
        }
        for (uint32_t n = 0; n < chunk_count; n++) {
            auto chunk = io->storage_pool().chunk(storage_pool::seq, n);
            if (chunk->size() != 0) {
                throw std::runtime_error(
                    "Trying to initialise new DB but storage pool contains "
                    "existing data, stopping now to prevent data loss.");
            }
        }
        memset(db_metadata_[0], 0, map_size);
        MONAD_DEBUG_ASSERT((chunk_count & ~0xfffffU) == 0);
        db_metadata_[0]->chunk_info_count = chunk_count & 0xfffffU;
        memset(
            &db_metadata_[0]->free_list,
            0xff,
            sizeof(db_metadata_[0]->free_list));
        memset(
            &db_metadata_[0]->fast_list,
            0xff,
            sizeof(db_metadata_[0]->fast_list));
        memset(
            &db_metadata_[0]->slow_list,
            0xff,
            sizeof(db_metadata_[0]->slow_list));
        auto *chunk_info =
            start_lifetime_as_array<detail::db_metadata::chunk_info_t>(
                db_metadata_[0]->chunk_info, chunk_count);
        for (size_t n = 0; n < chunk_count; n++) {
            auto &ci = chunk_info[n];
            ci.prev_chunk_id = ci.next_chunk_id =
                detail::db_metadata::chunk_info_t::INVALID_CHUNK_ID;
        }
        // magics are not set yet, so memcpy is fine here
        memcpy(db_metadata_[1], db_metadata_[0], map_size);

        // Insert all chunks into the free list
        std::vector<uint32_t> chunks;
        chunks.reserve(chunk_count);
        for (uint32_t n = 0; n < chunk_count; n++) {
            auto chunk = io->storage_pool().chunk(storage_pool::seq, n);
            MONAD_DEBUG_ASSERT(chunk->zone_id().first == storage_pool::seq);
            MONAD_DEBUG_ASSERT(chunk->zone_id().second == n);
            MONAD_ASSERT(chunk->size() == 0); // chunks must actually be free
            chunks.push_back(n);
        }
#if !MONAD_MPT_INITIALIZE_POOL_WITH_CONSECUTIVE_CHUNKS
        small_prng rand;
        random_shuffle(chunks.begin(), chunks.end(), rand);
#endif
        auto append_with_insertion_count_override = [&](chunk_list list,
                                                        uint32_t id) {
            append(list, id);
            if (initial_insertion_count_on_pool_creation_ != 0) {
                auto override_insertion_count = [&](detail::db_metadata *db) {
                    auto g = db->hold_dirty();
                    auto *i = db->at_(id);
                    i->insertion_count0_ =
                        uint32_t(initial_insertion_count_on_pool_creation_) &
                        0x3ff;
                    i->insertion_count1_ =
                        uint32_t(
                            initial_insertion_count_on_pool_creation_ >> 10) &
                        0x3ff;
                };
                override_insertion_count(db_metadata_[0]);
                override_insertion_count(db_metadata_[1]);
            }
            auto *i = db_metadata_[0]->at_(id);
            MONAD_ASSERT(i->index(db_metadata_[0]) == id);
        };
        // root offset is the front of fast list
        chunk_offset_t const fast_offset(chunks.front(), 0);
        append_with_insertion_count_override(chunk_list::fast, fast_offset.id);
        // init the first slow chunk and slow_offset
        chunk_offset_t const slow_offset(chunks[1], 0);
        append_with_insertion_count_override(chunk_list::slow, slow_offset.id);
        std::span const chunks_after_second(
            chunks.data() + 2, chunks.size() - 2);
        // insert the rest of the chunks to free list
        for (uint32_t const i : chunks_after_second) {
            append(chunk_list::free, i);
            auto *i_ = db_metadata_[0]->at_(i);
            MONAD_ASSERT(i_->index(db_metadata_[0]) == i);
        }

        // Mark as done, init root offset and history versions for the new
        // database as invalid
        advance_db_offsets_to(fast_offset, slow_offset);
        db_metadata_[0]->root_offsets.reset_all(0);
        db_metadata_[1]->root_offsets.reset_all(0);

        // Set history length
        update_history_length_metadata(history_len);

        std::atomic_signal_fence(
            std::memory_order_seq_cst); // no compiler reordering here
        memcpy(
            db_metadata_[0]->magic,
            detail::db_metadata::MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);
        memcpy(
            db_metadata_[1]->magic,
            detail::db_metadata::MAGIC,
            detail::db_metadata::MAGIC_STRING_LEN);

        if (!io->is_read_only()) {
            // Default behavior: initialize node writers to start at the
            // start of available slow and fast list respectively. Make sure
            // the initial fast/slow offset points into a block in use as a
            // sanity check
            reset_node_writers();
        }
    }
    else { // resume from an existing db and underlying storage devices
        if (!io->is_read_only()) {
            // Reset/init node writer's offsets, destroy contents after
            // fast_offset.id chunck
            rewind_to_match_offsets();
        }
    }
    // If the pool has changed since we configured the metadata, this will
    // fail
    MONAD_ASSERT(db_metadata_[0]->chunk_info_count == chunk_count);
}
#if defined(__GNUC__) && !defined(__clang__)
    #pragma GCC diagnostic pop
#endif

void UpdateAuxImpl::unset_io()
{
    node_writer_fast.reset();
    node_writer_slow.reset();
    auto const chunk_count = io->chunk_count();
    auto const map_size =
        sizeof(detail::db_metadata) +
        chunk_count * sizeof(detail::db_metadata::chunk_info_t);
    (void)::munmap(db_metadata_[0], map_size);
    (void)::munmap(db_metadata_[1], map_size);
    io = nullptr;
}

Node::UniquePtr
UpdateAuxImpl::read_node_from_buffers(chunk_offset_t const offset) const
{
    auto const &write_back_buffer = db_metadata()->at(offset.id)->in_fast_list
                                        ? write_back_buffer_fast
                                        : write_back_buffer_slow;
    auto const virtual_offset = physical_to_virtual(offset);
    if (write_back_buffer.contains(virtual_offset)) {
        auto curr_offset = write_back_buffer.virtual_offset_begin;
        auto it = write_back_buffer.items.begin();
        for (; it != write_back_buffer.items.end(); ++it) {
            if (it->contains(offset)) { // found it
                break;
            }
            curr_offset += it->size();
        }
        MONAD_ASSERT(curr_offset <= virtual_offset.raw());
        auto buffer_off =
            static_cast<unsigned>(virtual_offset.raw() - curr_offset);
        // sometimes it takes multiple buffers to deserialize
        // First get the disk size
        // Then allocate the node, loop through buffer until finish
        // copying all bytes
        MONAD_ASSERT(it->size() > buffer_off);
        auto const disk_size = unaligned_load<uint32_t>(
            (unsigned char *)it->buffer.data() + buffer_off);
        MONAD_ASSERT(disk_size > 0);
        buffer_off += Node::disk_size_bytes;
        auto const mask = unaligned_load<uint16_t>(
            (unsigned char *)it->buffer.data() + buffer_off);
        // TODO: THIS ASSERTION does not necessarily have to be true
        MONAD_ASSERT((unsigned)it->size() - buffer_off >= disk_size);
        auto const number_of_children =
            static_cast<unsigned>(std::popcount(mask));
        auto const alloc_size = static_cast<uint32_t>(
            disk_size + number_of_children * sizeof(Node *) -
            Node::disk_size_bytes);
        auto node = Node::make(alloc_size);
        // continue load disk size and mask from next buffer
        // loop through buffers to copy all remaining bytes
        auto node_remaining_bytes = disk_size - Node::disk_size_bytes;
        unsigned offset_in_node = 0;
        while (node_remaining_bytes > 0) {
            unsigned const bytes_to_copy = std::min(
                node_remaining_bytes, (unsigned)it->size() - buffer_off);
            if (bytes_to_copy < node_remaining_bytes) {
                std::cout << "need to continue reading from next buffer"
                          << std::endl;
            }
            std::copy_n(
                (unsigned char *)it->buffer.data() + buffer_off,
                bytes_to_copy,
                (unsigned char *)node.get() + offset_in_node);
            node_remaining_bytes -= bytes_to_copy;
            MONAD_ASSERT(node_remaining_bytes == 0);
            offset_in_node += bytes_to_copy;
            // // update to next buffer
            // if (buffer_off + bytes_to_copy == it->size()) {
            //     MONAD_ASSERT(false);
            //     buffer_off = 0;
            //     ++it;
            //     MONAD_ASSERT(it != write_back_buffer.items.end());
            // }
        }
        std::memset(node->next_data(), 0, number_of_children * sizeof(Node *));
        MONAD_ASSERT(node->get_mem_size() == alloc_size);
        return node;
    }
    return {};
}

void UpdateAuxImpl::reset_node_writers()
{
    auto init_node_writer =
        [&](chunk_offset_t const node_writer_offset,
            bool const is_fast) -> node_writer_unique_ptr_type {
        auto chunk =
            io->storage_pool().chunk(storage_pool::seq, node_writer_offset.id);
        MONAD_ASSERT(chunk->size() >= node_writer_offset.offset);
        return io ? make_connected_writer(
                        is_fast,
                        node_writer_offset,
                        std::min(
                            AsyncIO::WRITE_BUFFER_SIZE,
                            size_t(
                                chunk->capacity() - node_writer_offset.offset)))
                  : node_writer_unique_ptr_type{};
    };
    node_writer_fast = init_node_writer(
        db_metadata()->db_offsets.start_of_wip_offset_fast, true);
    node_writer_slow = init_node_writer(
        db_metadata()->db_offsets.start_of_wip_offset_slow, false);
}

node_writer_unique_ptr_type UpdateAuxImpl::make_connected_writer(
    bool const is_fast, chunk_offset_t const writer_offset,
    size_t const bytes_to_write)
{
    MONAD_ASSERT(io != nullptr);
    // append that writer to buffered writes
    filled_write_buffer sender_buffer{bytes_to_write};
    sender_buffer.set_write_buffer(io->get_write_buffer());
    MONAD_ASSERT(sender_buffer.size() == bytes_to_write);
    auto &write_back_buffer =
        is_fast ? write_back_buffer_fast : write_back_buffer_slow;
    // write back buffer owns it
    write_back_buffer.push(BufferedWriteInfo{
        .offset = writer_offset, .buffer = std::move(sender_buffer)});
    // sender doesn't own it
    return io->make_connected(
        write_no_owning_buffer_sender{
            writer_offset, write_back_buffer.items.back().buffer},
        write_operation_io_receiver{*this, is_fast});
}

/* upsert() supports both on disk and in memory db updates. User should
always use this interface to upsert updates to db. Here are what it does:
- if `compaction`, erase outdated history block if any, and update
compaction offsets;
- copy state from last version to new version if new version not yet exist;
- upsert `updates` should include everything nested under
version number;
- if it's on disk, update db_metadata min max versions.

Note that `version` on each call of upsert() is either the max version or max
version + 1. However, we do not assume that the version history is continuous
because user can move_trie_version_forward(), which can invalidate versions in
the middle of a continuous history.
*/
Node::UniquePtr UpdateAuxImpl::do_update(
    Node::UniquePtr prev_root, StateMachine &sm, UpdateList &&updates,
    uint64_t const version, bool const compaction, bool const can_write_to_fast)
{
    auto g(unique_lock());
    auto g2(set_current_upsert_tid());

    if (is_in_memory()) {
        return upsert(
            *this, version, sm, std::move(prev_root), std::move(updates));
    }
    MONAD_ASSERT(is_on_disk());
    set_can_write_to_fast(can_write_to_fast);

    auto const max_version = db_history_max_version();
    MONAD_ASSERT(
        max_version == INVALID_BLOCK_ID || version == max_version ||
        version == max_version + 1);
    // Erase the earliest valid version if it is going to be outdated after
    // upserting new version, advance compaction offsets

    // TODO: do not start compaction or invalidate block if disk usage is lower
    // than 30% unless history exceeds metadata ring buffer capacity.
    // TODO: increase disk ring buffer capacity to ~1M slots.
    auto const min_valid_version = db_history_min_valid_version();
    auto const version_history_len = version_history_length();
    if (min_valid_version != INVALID_BLOCK_ID /* at least one valid version */
        && version - min_valid_version >= version_history_len) {
        if (compaction) {
            // this step may remove more blocks and free disk chunks
            advance_compact_offsets(min_valid_version);
        }
        else {
            // erase min_valid_version, must happen before upsert() because that
            // offset slot in ring buffer may be overwritten thus invalidated in
            // `upsert()`.
            update_root_offset(min_valid_version, INVALID_OFFSET);
        }
    }
    auto root =
        upsert(*this, version, sm, std::move(prev_root), std::move(updates));
    MONAD_DEBUG_ASSERT(
        version - db_history_min_valid_version() + 1 <=
        version_history_length());

    return root;
}

void UpdateAuxImpl::move_trie_version_forward(
    uint64_t const src, uint64_t const dest)
{
    MONAD_ASSERT(is_on_disk());
    // only allow moving forward
    MONAD_ASSERT(
        dest > src && dest != INVALID_BLOCK_ID &&
        dest >= db_history_max_version());
    auto g(unique_lock());
    auto g2(set_current_upsert_tid());
    auto const offset = get_latest_root_offset();
    update_root_offset(src, INVALID_OFFSET);
    fast_forward_next_version(dest);
    append_root_offset(offset);
}

std::pair<uint32_t, uint32_t>
UpdateAuxImpl::min_offsets_of_version(uint64_t const version)
{
    // TODO: can save a blocking read if we store the min_offset_fast/slow to
    // the version ring buffer in metadata
    auto const erase_root_offset = get_root_offset_at_version(version);
    Node::UniquePtr root_to_erase = read_node_from_buffers(erase_root_offset);
    if (!root_to_erase) {
        root_to_erase.reset(
            read_node_blocking(io->storage_pool(), erase_root_offset));
    }

    auto [min_offset_fast, min_offset_slow] = calc_min_offsets(*root_to_erase);
    if (min_offset_fast == INVALID_COMPACT_VIRTUAL_OFFSET) {
        min_offset_fast = MIN_COMPACT_VIRTUAL_OFFSET;
    }
    if (min_offset_slow == INVALID_COMPACT_VIRTUAL_OFFSET) {
        min_offset_slow = MIN_COMPACT_VIRTUAL_OFFSET;
    }
    return {min_offset_fast.get_count(), min_offset_slow.get_count()};
}

uint32_t divide_and_round(uint32_t const dividend, uint64_t const divisor)
{
    MONAD_ASSERT(divisor != 0);
    double const result = dividend / static_cast<double>(divisor);
    auto const result_floor = static_cast<uint32_t>(std::floor(result));
    double const fractional = result - result_floor;
    auto const r = static_cast<double>(rand()) / RAND_MAX;
    return result_floor + static_cast<uint32_t>(r <= fractional);
}

void UpdateAuxImpl::advance_compact_offsets(uint64_t version_to_erase)
{
    /* A note on ring based compaction:
    Fast list compaction is steady pace based on disk growth over recent blocks,
    and we assume no large sets of upsert work directly committed to fast list,
    meaning no greater than per block updates, otherwise there could be large
    amount of data compacted in one block.
    Large set of states upsert, like snapshot loading or state sync, should be
    written in slow ring. It is under the assumption that only small set of
    states are updated often, majority is not going to be updated in a while, so
    when block execution starts we don’t need to waste disk bandwidth to copy
    them from fast to slow.

    Compaction offset update algo:
    The fast ring is compacted at a steady pace based on the average disk growth
    observed over recent blocks. We define two disk usage thresholds:
    `usage_limit_start_compact_slow` and `usage_limit`. When disk usage reaches
    `usage_limit_start_compact_slow`, slow ring compaction begins, guided by the
    slow ring garbage collection ratio from the last block. If disk usage
    exceeds `usage_limit`, the system will start shortening the history until
    disk usage is brought back within the threshold.
    */
    MONAD_ASSERT(is_on_disk());
    // update disk growth speed trackers
    auto fast_offset = node_writer_fast->sender().offset();
    fast_offset.offset = (fast_offset.offset +
                          node_writer_fast->sender().written_buffer_bytes()) &
                         chunk_offset_t::max_offset;
    compact_virtual_chunk_offset_t const curr_fast_writer_offset{
        physical_to_virtual(fast_offset)};
    auto slow_offset = node_writer_slow->sender().offset();
    slow_offset.offset = (slow_offset.offset +
                          node_writer_slow->sender().written_buffer_bytes()) &
                         chunk_offset_t::max_offset;
    compact_virtual_chunk_offset_t const curr_slow_writer_offset{
        physical_to_virtual(slow_offset)};
    last_block_disk_growth_fast_ =
        last_block_end_offset_fast_ == 0
            ? MIN_COMPACT_VIRTUAL_OFFSET
            : curr_fast_writer_offset - last_block_end_offset_fast_;
    last_block_disk_growth_slow_ =
        last_block_end_offset_slow_ == 0
            ? MIN_COMPACT_VIRTUAL_OFFSET
            : curr_slow_writer_offset - last_block_end_offset_slow_;
    last_block_end_offset_fast_ = curr_fast_writer_offset;
    last_block_end_offset_slow_ = curr_slow_writer_offset;

    compact_offset_fast = db_metadata()->db_offsets.last_compact_offset_fast;
    compact_offset_slow = db_metadata()->db_offsets.last_compact_offset_slow;
    compact_offset_range_fast_ = MIN_COMPACT_VIRTUAL_OFFSET;

    auto used_chunks_ratio = [&] -> double {
        return 1 -
               (double)num_chunks(chunk_list::free) / (double)io->chunk_count();
    };
    /* Compact the fast ring based on average disk growth over recent blocks. */
    auto const max_version = db_history_max_version();
    MONAD_ASSERT(
        version_to_erase != INVALID_BLOCK_ID &&
        version_to_erase != db_history_max_version());
    std::tie(
        chunks_to_remove_before_count_fast_,
        chunks_to_remove_before_count_slow_) =
        min_offsets_of_version(version_to_erase);
    if (auto const virtual_root_offset =
            physical_to_virtual(get_root_offset_at_version(version_to_erase));
        virtual_root_offset.in_fast_list()) {
        MONAD_ASSERT(version_history_length() > 1);
        auto const compacted_erased_root_offset =
            compact_virtual_chunk_offset_t{virtual_root_offset};
        MONAD_ASSERT(curr_fast_writer_offset >= compacted_erased_root_offset);
        compact_offset_range_fast_.set_value(divide_and_round(
            curr_fast_writer_offset - compacted_erased_root_offset,
            max_version - version_to_erase));
        compact_offset_fast += compact_offset_range_fast_;
    }
    update_root_offset(version_to_erase, INVALID_OFFSET);
    free_compacted_chunks(); // Free released chunks here because the history
                             // length adjustment is based on current disk usage

    double const usage_limit_start_compact_slow = 0.6;
    double const usage_limit = 0.8;
    if (used_chunks_ratio() > usage_limit) {
        // Shorten the history length
        while (used_chunks_ratio() > usage_limit) {
            version_to_erase = db_history_min_valid_version();
            MONAD_ASSERT(version_to_erase != INVALID_BLOCK_ID);
            if (version_to_erase == max_version) {
                // the only version left, no more to erase
                break;
            }
            std::tie(
                chunks_to_remove_before_count_fast_,
                chunks_to_remove_before_count_slow_) =
                min_offsets_of_version(version_to_erase);
            update_root_offset(version_to_erase, INVALID_OFFSET);
            free_compacted_chunks();
            update_history_length_metadata(max_version - version_to_erase);
        }
    }
    if (used_chunks_ratio() > usage_limit_start_compact_slow) {
        // Compact slow ring: the offset is based on slow list garbage
        // collection ratio of last block
        compact_offset_range_slow_.set_value(
            (stats.compacted_bytes_in_slow != 0 &&
             compact_offset_range_slow_ != 0)
                ? std::min(
                      (uint32_t)last_block_disk_growth_slow_ + 1,
                      (uint32_t)std::round(
                          double(compact_offset_range_slow_ << 16) /
                          stats.compacted_bytes_in_slow))
                : 1);
        compact_offset_slow += compact_offset_range_slow_;
    }
}

uint64_t UpdateAuxImpl::version_history_length() const noexcept
{
    return start_lifetime_as<std::atomic_uint64_t const>(
               &db_metadata()->history_length)
        ->load(std::memory_order_relaxed);
}

uint64_t UpdateAuxImpl::db_history_min_valid_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto &offsets = db_metadata()->root_offsets;
    auto min_version = db_history_range_lower_bound();
    for (; min_version != offsets.max_version(); ++min_version) {
        if (offsets[min_version] != INVALID_OFFSET) {
            break;
        }
    }
    return min_version;
}

uint64_t UpdateAuxImpl::db_history_range_lower_bound() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    auto const max_version = db_history_max_version();
    if (max_version == INVALID_BLOCK_ID) {
        return INVALID_BLOCK_ID;
    }
    else {
        return (max_version >= version_history_length() - 1)
                   ? (max_version - version_history_length() + 1)
                   : 0;
    }
}

uint64_t UpdateAuxImpl::db_history_max_version() const noexcept
{
    MONAD_ASSERT(is_on_disk());
    return db_metadata()->get_max_version_in_history();
}

void UpdateAuxImpl::free_compacted_chunks()
{
    auto free_chunks_from_ci_till_count =
        [&](detail::db_metadata::chunk_info_t const *ci,
            uint32_t const count_before) {
            uint32_t idx = ci->index(db_metadata());
            uint32_t count =
                (uint32_t)db_metadata()->at(idx)->insertion_count();
            for (; count < count_before && ci != nullptr;
                 idx = ci->index(db_metadata()),
                 count = (uint32_t)db_metadata()->at(idx)->insertion_count()) {
                ci = ci->next(db_metadata()); // must be in this order
                remove(idx);
                io->storage_pool()
                    .chunk(monad::async::storage_pool::seq, idx)
                    ->destroy_contents();
                append(
                    UpdateAuxImpl::chunk_list::free,
                    idx); // append not prepend
            }
        };
    MONAD_ASSERT(
        chunks_to_remove_before_count_fast_ <=
        db_metadata()->fast_list_end()->insertion_count());
    MONAD_ASSERT(
        chunks_to_remove_before_count_slow_ <=
        db_metadata()->slow_list_end()->insertion_count());
    free_chunks_from_ci_till_count(
        db_metadata()->fast_list_begin(), chunks_to_remove_before_count_fast_);
    free_chunks_from_ci_till_count(
        db_metadata()->slow_list_begin(), chunks_to_remove_before_count_slow_);
}

uint32_t UpdateAuxImpl::num_chunks(chunk_list const list) const noexcept
{
    switch (list) {
    case chunk_list::free:
        // Triggers when out of storage
        MONAD_ASSERT(db_metadata_[0]->free_list_begin() != nullptr);
        MONAD_ASSERT(db_metadata_[0]->free_list_end() != nullptr);

        return (uint32_t)(db_metadata_[0]->free_list_end()->insertion_count() -
                          db_metadata_[0]
                              ->free_list_begin()
                              ->insertion_count()) +
               1;
    case chunk_list::fast:
        // Triggers when out of storage
        MONAD_ASSERT(db_metadata_[0]->fast_list_begin() != nullptr);
        MONAD_ASSERT(db_metadata_[0]->fast_list_end() != nullptr);

        return (uint32_t)(db_metadata_[0]->fast_list_end()->insertion_count() -
                          db_metadata_[0]
                              ->fast_list_begin()
                              ->insertion_count()) +
               1;
    case chunk_list::slow:
        // Triggers when out of storage
        MONAD_ASSERT(db_metadata_[0]->slow_list_begin() != nullptr);
        MONAD_ASSERT(db_metadata_[0]->slow_list_end() != nullptr);

        return (uint32_t)(db_metadata_[0]->slow_list_end()->insertion_count() -
                          db_metadata_[0]
                              ->slow_list_begin()
                              ->insertion_count()) +
               1;
    }
    return 0;
}

void UpdateAuxImpl::print_update_stats()
{
#if MONAD_MPT_COLLECT_STATS
    printf(
        "======\n"
        "nodes created or updated: %u\n",
        stats.nodes_created_or_updated);

    if (compact_offset_fast) {
        printf(
            "------\n"
            "Ring  |  Copied  | CompactRange | Ratio \n"
            "Fast  |  %5ukb |  %7ukb   | %.2f%%\n",
            stats.compacted_bytes_in_fast >> 10,
            compact_offset_range_fast_ << 6,
            100.0 * stats.compacted_bytes_in_fast /
                (compact_offset_range_fast_ << 16));
        if (compact_offset_range_slow_) {
            printf(
                "Slow  |  %5ukb |  %7ukb   | %.2f%%\n",
                stats.compacted_bytes_in_slow >> 10,
                compact_offset_range_slow_ << 6,
                100.0 * stats.compacted_bytes_in_slow /
                    (compact_offset_range_slow_ << 16));
        }

        // slow list compaction range vs growth
        auto const total_bytes_written_to_slow =
            stats.compacted_bytes_in_fast + stats.compacted_bytes_in_slow;
        printf(
            "------\n"
            "Slow ring data written\n"
            "%8s |%8s |%10s |%10s |%8s |  %s\n"
            " %6ukb |%6ukb |%8ukb |%8ukb |%6ukb |  %.2f%%\n",
            "Compacted",
            "F-S",
            "active S-S",
            "other S-F",
            "Total",
            "Written/Compacted",
            compact_offset_range_slow_ << 6,
            stats.compacted_bytes_in_fast >> 10,
            stats.compacted_bytes_in_slow >> 10,
            stats.bytes_copied_slow_to_fast_for_slow >> 10,
            total_bytes_written_to_slow >> 10,
            100.0 * total_bytes_written_to_slow /
                (compact_offset_range_slow_ << 16));

        // num nodes copied:
        auto const nodes_copied_for_slow =
            stats.compacted_nodes_in_fast +
            stats.nodes_copied_fast_to_fast_for_fast;
        printf(
            "------\nNodes copied\n"
            "Fast: active F-S %u (%.2f%%), F-F %u "
            "(%.2f%%)\n",
            stats.compacted_nodes_in_fast,
            100.0 * stats.compacted_nodes_in_fast / (nodes_copied_for_slow),
            stats.nodes_copied_fast_to_fast_for_fast,
            100.0 * stats.nodes_copied_fast_to_fast_for_fast /
                nodes_copied_for_slow);
        if (compact_offset_slow) {
            auto const nodes_copied_for_slow =
                stats.compacted_nodes_in_slow +
                stats.nodes_copied_fast_to_fast_for_slow +
                stats.nodes_copied_slow_to_fast_for_slow;
            printf(
                "Slow: active S-S %u (%.2f%%), F-F %u (%.2f%%), other S-F %u "
                "(%.2f%%)\n",
                stats.compacted_nodes_in_slow,
                100.0 * stats.compacted_nodes_in_slow / nodes_copied_for_slow,
                stats.nodes_copied_fast_to_fast_for_slow,
                100.0 * stats.nodes_copied_fast_to_fast_for_slow /
                    nodes_copied_for_slow,
                stats.nodes_copied_slow_to_fast_for_slow,
                100.0 * stats.nodes_copied_slow_to_fast_for_slow /
                    nodes_copied_for_slow);
        }
    }

    if (compact_offset_range_fast_) {
        printf(
            "------\n"
            "Fast: compact reads within compaction range %u / "
            "total compact reads %u = %.4f\n",
            stats.nreads_before_compact_offset[0],
            stats.nreads_before_compact_offset[0] +
                stats.nreads_after_compact_offset[0],
            (double)stats.nreads_before_compact_offset[0] /
                (stats.nreads_before_compact_offset[0] +
                 stats.nreads_after_compact_offset[0]));
        if (compact_offset_range_fast_) {
            printf(
                "Fast: bytes read within compaction range %.2fmb / "
                "compaction offset range %.2fmb = %.4f, bytes read out of "
                "compaction range %.2fmb\n",
                (double)stats.bytes_read_before_compact_offset[0] / 1024 / 1024,
                (double)compact_offset_range_fast_ / 16,
                (double)stats.bytes_read_before_compact_offset[0] /
                    compact_offset_range_fast_ / 1024 / 64,
                (double)stats.bytes_read_after_compact_offset[0] / 1024 / 1024);
        }
    }
    if (compact_offset_range_slow_) {
        printf(
            "Slow: reads within compaction range %u / "
            "total compact reads %u = %.4f\n",
            stats.nreads_before_compact_offset[1],
            stats.nreads_before_compact_offset[1] +
                stats.nreads_after_compact_offset[1],
            (double)stats.nreads_before_compact_offset[1] /
                (stats.nreads_before_compact_offset[1] +
                 stats.nreads_after_compact_offset[1]));
        printf(
            "Slow: bytes read within compaction range %.2fmb / "
            "compaction offset range %.2fmb = %.4f, bytes read out of "
            "compaction range %.2fmb\n",
            (double)stats.bytes_read_before_compact_offset[1] / 1024 / 1024,
            (double)compact_offset_range_slow_ / 16,
            (double)stats.bytes_read_before_compact_offset[1] /
                compact_offset_range_slow_ / 1024 / 64,
            (double)stats.bytes_read_after_compact_offset[1] / 1024 / 1024);
    }
    printf(
        "Fast list grow %u kb, Slow list grow %u kb\n",
        last_block_disk_growth_fast_ << 6,
        last_block_disk_growth_slow_ << 6);
#endif
}

void UpdateAuxImpl::reset_stats()
{
    stats.reset();
}

void UpdateAuxImpl::collect_number_nodes_created_stats()
{
#if MONAD_MPT_COLLECT_STATS
    ++stats.nodes_created_or_updated;
#endif
}

void UpdateAuxImpl::collect_compaction_read_stats(
    chunk_offset_t const physical_node_offset, unsigned const bytes_to_read)
{
#if MONAD_MPT_COLLECT_STATS
    auto const node_offset = physical_to_virtual(physical_node_offset);
    if (compact_virtual_chunk_offset_t(node_offset) <
        (node_offset.in_fast_list() ? compact_offset_fast
                                    : compact_offset_slow)) {
        // node orig offset in fast list but compact to slow list
        ++stats.nreads_before_compact_offset[!node_offset.in_fast_list()];
        stats.bytes_read_before_compact_offset[!node_offset.in_fast_list()] +=
            bytes_to_read; // compaction bytes read
    }
    else {
        ++stats.nreads_after_compact_offset[!node_offset.in_fast_list()];
        stats.bytes_read_after_compact_offset[!node_offset.in_fast_list()] +=
            bytes_to_read;
    }
    ++stats.nreads_compaction; // count number of compaction reads
#else
    (void)physical_node_offset;
    (void)bytes_to_read;
#endif
}

void UpdateAuxImpl::collect_compacted_nodes_stats(
    bool const copy_node_for_fast, bool const rewrite_to_fast,
    virtual_chunk_offset_t node_offset, uint32_t node_disk_size)
{
#if MONAD_MPT_COLLECT_STATS
    if (copy_node_for_fast) {
        MONAD_ASSERT(node_offset.in_fast_list());
        if (rewrite_to_fast) {
            ++stats.nodes_copied_fast_to_fast_for_fast;
        }
        else {
            ++stats.compacted_nodes_in_fast;
            stats.compacted_bytes_in_fast += node_disk_size;
        }
    }
    else { // copy node for slow
        if (rewrite_to_fast) {
            if (node_offset.in_fast_list()) {
                ++stats.nodes_copied_fast_to_fast_for_slow;
            }
            else {
                ++stats.nodes_copied_slow_to_fast_for_slow;
                stats.bytes_copied_slow_to_fast_for_slow += node_disk_size;
            }
        }
        else { // rewrite to slow
            MONAD_ASSERT(!node_offset.in_fast_list());
            MONAD_ASSERT(
                compact_virtual_chunk_offset_t{node_offset} <
                compact_offset_slow);
            ++stats.compacted_nodes_in_slow;
            stats.compacted_bytes_in_slow += node_disk_size;
        }
    }
#else
    if (!copy_node_for_fast && !rewrite_to_fast) {
        MONAD_ASSERT(!node_offset.in_fast_list());
        MONAD_ASSERT(
            compact_virtual_chunk_offset_t{node_offset} < compact_offset_slow);
        stats.compacted_bytes_in_slow += node_disk_size;
    }
    (void)copy_node_for_fast;
    (void)rewrite_to_fast;
#endif
}

MONAD_MPT_NAMESPACE_END
