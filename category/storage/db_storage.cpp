#include <category/storage/db_storage.hpp>

#include <chrono>
#include <filesystem>
#include <thread>

#include <errno.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

MONAD_STORAGE_NAMESPACE_BEGIN

void DbStorage::init_(int const fd, Mode const mode, creation_flags const flags)
{
    // Sanity checks for mode and flags compatibility
    MONAD_ASSERT(
        !(flags.open_read_only || flags.open_read_only_allow_dirty) ||
            mode == Mode::open_existing,
        "Read-only flags require mode::open_existing");
    MONAD_ASSERT(
        mode != Mode::truncate ||
            !(flags.open_read_only || flags.open_read_only_allow_dirty),
        "Cannot truncate storage pool in read-only mode");

    is_read_only_ = flags.open_read_only;
    is_read_only_allow_dirty_ = flags.open_read_only_allow_dirty;
    is_newly_truncated_ = (mode == Mode::truncate);
    fd_ = fd;

    struct stat stat;
    MONAD_ASSERT_PRINTF(
        -1 != ::fstat(fd_, &stat), "Failed to stat file %s", strerror(errno));
    // device_type_ and size_of_device_
    if ((stat.st_mode & S_IFMT) == S_IFBLK) {
        device_type_ = type_t_::block_device;
        MONAD_ASSERT_PRINTF(
            ioctl(
                fd_, _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/, &stat.st_size) ==
                0,
            "Failed to get size: %s",
            strerror(errno));
        size_of_device_ = static_cast<size_t>(stat.st_size);
    }
    else if ((stat.st_mode & S_IFMT) == S_IFREG) {
        device_type_ = type_t_::file;
        size_of_device_ = static_cast<size_t>(stat.st_size);
    }
    else {
        MONAD_ABORT_PRINTF(
            "Storage source has unknown file entry type = %u",
            (stat.st_mode & S_IFMT));
    }

    unique_hash_ = fnv1a_hash<uint32_t>::begin();
    fnv1a_hash<uint32_t>::add(unique_hash_, uint32_t(device_type_));
    fnv1a_hash<uint32_t>::add(unique_hash_, uint32_t(size_of_device_));

    verify_and_map_chunk_metadata_(mode);
    MONAD_ASSERT(num_chunks() == chunk_metadata_t::num_chunks(size_of_device_));

    // if open_existing, do integrity check with hash and metadata magic
    // string
    init_db_metadata_(); // which initialize root offsets ring buffer too

    chunks_data_ = (unsigned char *)::mmap(
        nullptr,
        chunk_capacity * num_chunks(),
        PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
        -1,
        0);
    MONAD_ASSERT(chunks_data_ != MAP_FAILED);
    file_mmap_helper_(
        chunk_capacity * num_chunks(), 0, chunks_data_, MAP_FIXED);

    if (flags.madv_random_access) {
        // Use MADV_RANDOM to optimize for random access patterns
        MONAD_ASSERT_PRINTF(
            ::madvise(
                chunks_data_, chunk_capacity * num_chunks(), MADV_RANDOM) == 0,
            "failed to madvise(MADV_RANDOM): %s",
            strerror(errno));
    }
}

DbStorage::DbStorage(use_anonymous_inode_tag, off_t const len)
{
    int const fd = make_temporary_inode();
    MONAD_ASSERT_PRINTF(
        -1 != ::ftruncate(fd, len),
        "Failed to truncate temporary inode: %s",
        strerror(errno));

    init_(fd, Mode::create_if_needed);
}

DbStorage::DbStorage(
    std::filesystem::path const path, Mode const mode,
    creation_flags const flags)
{
    int const fd = open(
        path.c_str(),
        ((flags.open_read_only || flags.open_read_only_allow_dirty) ? O_RDONLY
                                                                    : O_RDWR) |
            O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1, "Failed to open file %s: %s", path.c_str(), strerror(errno));
    init_(fd, mode, flags);
}

DbStorage::~DbStorage()
{
    // TODO: require msync for writable db?
    if (chunks_data_ != nullptr) {
        auto const map_size = chunk_capacity * num_chunks();
        MONAD_ASSERT_PRINTF(
            ::munmap(chunks_data_, map_size) != -1,
            "failed to munmap: %s",
            strerror(errno));
    }
    auto const chunk_count = num_chunks();
    if (chunk_metadata_ != nullptr) {
        auto const total_size = chunk_metadata_->total_size(size_of_device_);
        uintptr_t const metadata_start =
            (uintptr_t)chunk_metadata_ + sizeof(chunk_metadata_t) - total_size;
        uintptr_t const map_base =
            round_down_align<CPU_PAGE_BITS>(metadata_start);
        auto const map_size = total_size + (metadata_start - map_base);
        MONAD_ASSERT((map_size & (CPU_PAGE_SIZE - 1)) == 0);
        MONAD_ASSERT(map_base <= metadata_start)

        MONAD_ASSERT_PRINTF(
            ::munmap(
                reinterpret_cast<void *>(map_base),
                total_size + (metadata_start - map_base)) != -1,
            "failed to munmap: %s",
            strerror(errno));
        chunks_data_ = nullptr;
    }

    for (auto const i : {0, 1}) {
        // unmap root offsets
        if (db_metadata_[0].root_offsets.data() != nullptr) {
            MONAD_ASSERT_PRINTF(
                ::munmap(
                    db_metadata_[i].root_offsets.data(),
                    db_metadata_[i].root_offsets.size_bytes()) != -1,
                "failed to munmap: %s",
                strerror(errno));
            db_metadata_[i].root_offsets = {};
        }
        // unmap db_metadata main
        if (db_metadata_[i].main != nullptr) {
            auto const map_size =
                sizeof(detail::db_metadata_t) +
                chunk_count * sizeof(detail::db_metadata_t::chunk_info_t);
            MONAD_ASSERT_PRINTF(
                ::munmap(db_metadata_[i].main, map_size) != -1,
                "failed to munmap: %s",
                strerror(errno));
            db_metadata_[i].main = nullptr;
        }
    }

    if (fd_ != -1) {
        (void)::close(fd_);
    }
}

uint32_t DbStorage::compute_config_hash_()
{
    auto hashshouldbe = fnv1a_hash<uint32_t>::begin();
    fnv1a_hash<uint32_t>::add(hashshouldbe, uint32_t(unique_hash_));
    fnv1a_hash<uint32_t>::add(hashshouldbe, uint32_t(unique_hash_ >> 32));

    fnv1a_hash<uint32_t>::add(hashshouldbe, uint32_t(num_chunks()));
    fnv1a_hash<uint32_t>::add(hashshouldbe, chunk_capacity);

    return static_cast<uint32_t>(hashshouldbe);
}

void *DbStorage::file_mmap_helper_(
    size_t const size, file_offset_t const offset, void *const map_address,
    int const additional_flags)
{
    auto const prot = (is_read_only_ && !is_read_only_allow_dirty_)
                          ? PROT_READ
                          : (PROT_READ | PROT_WRITE);
    auto const mapflags =
        additional_flags |
        (is_read_only_allow_dirty_ ? MAP_PRIVATE : MAP_SHARED);
    void *data = mmap(map_address, size, prot, mapflags, fd_, (off_t)offset);
    MONAD_ASSERT_PRINTF(
        data != MAP_FAILED, "Failed to mmap file: %s", strerror(errno));
    return data;
}

void DbStorage::verify_and_map_chunk_metadata_(DbStorage::Mode const op)
{
    auto const total_metadata_size =
        chunk_metadata_t::total_size(size_of_device_);
    // mmap must be aligned to CPU_PAGE_SIZE
    auto const map_offset = round_down_align<CPU_PAGE_BITS>(
        static_cast<size_t>(size_of_device_) - total_metadata_size);
    auto const map_size = round_up_align<CPU_PAGE_BITS>(
        static_cast<size_t>(size_of_device_) - map_offset);

    // TODO: either have both data and size or have none as member variable
    auto *const map_data = file_mmap_helper_(map_size, map_offset, nullptr, 0);
    MONAD_ASSERT_PRINTF(
        map_data != MAP_FAILED, "mmap failed: %s", strerror(errno));
    chunk_metadata_ = start_lifetime_as<chunk_metadata_t>(
        reinterpret_cast<std::byte *>(map_data) + size_of_device_ - map_offset -
        sizeof(chunk_metadata_t));

    if (memcmp(
            chunk_metadata_->magic,
            chunk_metadata_t::MAGIC,
            chunk_metadata_t::MAGIC_STRING_LEN) != 0 ||
        op == Mode::truncate) {
        // Uninitialized
        if (op == Mode::open_existing) {
            MONAD_ABORT("The source device has not been initialised for "
                        "use with storage pool");
        }
        if (size_of_device_ <
            chunk_capacity * (1 + chunk_metadata_t::reserved_chunks) +
                CPU_PAGE_SIZE) {
            MONAD_ABORT(
                "The source device must be at least chunk_capacity + 4Kb "
                "long other than the reserved chunks to be initialised for "
                "use with storage pool");
        }
        // Throw away all contents
        switch (device_type_) {
        case type_t_::file:
            if (-1 == ::ftruncate(fd_, 0)) {
                throw std::system_error(errno, std::system_category());
            }
            if (-1 == ::ftruncate(fd_, (off_t)size_of_device_)) {
                throw std::system_error(errno, std::system_category());
            }
            break;
        case type_t_::block_device: {
            uint64_t range[2] = {0, uint64_t(size_of_device_)};
            if (ioctl(fd_, _IO(0x12, 119) /*BLKDISCARD*/, &range)) {
                throw std::system_error(errno, std::system_category());
            }
            break;
        }
        default:
            MONAD_ABORT();
        }
        // initialize metadata on the mapping
        auto const chunk_bytes_used_array_size =
            total_metadata_size - sizeof(chunk_metadata_t);
        // boundary check
        MONAD_ASSERT(
            (std::byte *)chunk_metadata_ - chunk_bytes_used_array_size >=
            map_data);
        memset(
            (std::byte *)chunk_metadata_ - chunk_bytes_used_array_size,
            0,
            chunk_bytes_used_array_size);
        memcpy(
            chunk_metadata_->magic,
            chunk_metadata_t::MAGIC,
            chunk_metadata_t::MAGIC_STRING_LEN);
        chunk_metadata_->config_hash = compute_config_hash_();
    }
    else if (chunk_metadata_->config_hash != compute_config_hash_()) {
        MONAD_ABORT(
            "The srouce device has was initialised with a configuration "
            "different to this storage pool.\n\nYou should use the "
            "monad_mpt "
            "tool to copy and move databases around, NOT by copying "
            "partition "
            "contents!");
    }
}

void DbStorage::init_db_metadata_()
{
    auto const chunk_count = num_chunks();
    MONAD_ASSERT(chunk_count > 0);
    MONAD_ASSERT(chunk_count < std::numeric_limits<uint32_t>::max());
    auto const start_offset = db_metadata_offset();
    auto const map_size =
        sizeof(detail::db_metadata_t) +
        chunk_count * sizeof(detail::db_metadata_t::chunk_info_t);
    MONAD_ASSERT_PRINTF(
        map_size <= chunk_capacity / 2,
        "db_metadata size %zu exceeds half of chunk capacity %u",
        map_size,
        chunk_capacity / 2);

    db_metadata_[0].main = start_lifetime_as<detail::db_metadata_t>(
        file_mmap_helper_(map_size, start_offset.raw(), nullptr, 0));
    MONAD_ASSERT(db_metadata_[0].main != MAP_FAILED);
    db_metadata_[1].main =
        start_lifetime_as<detail::db_metadata_t>(file_mmap_helper_(
            map_size, start_offset.raw() + chunk_capacity / 2, nullptr, 0));
    MONAD_ASSERT(db_metadata_[1].main != MAP_FAILED);

    /* If on a storage which ignores TRIM, and the user just truncated
   an existing triedb, all the magics will be valid but the pool has
   been reset. Solve this by detecting when a pool has just been truncated
   and ensure all triedb structures are also reset.
   */
    if (is_newly_truncated_) {
        // If the pool has just been truncated, clear all metadata to force
        // a reconfiguration
        memset(
            db_metadata_[0].main->magic,
            0,
            sizeof(db_metadata_[0].main->magic));
        memset(
            db_metadata_[1].main->magic,
            0,
            sizeof(db_metadata_[1].main->magic));
    }
    auto const can_write_to_map = !is_read_only_ || is_read_only_allow_dirty_;
    /* If the front copy vanished for some reason ... this can happen
    if something or someone zaps the front bytes of the partition.
    */
    if (0 != memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata_t::MAGIC,
                 detail::db_metadata_t::MAGIC_STRING_LEN)) {
        if (0 == memcmp(
                     db_metadata_[1].main->magic,
                     detail::db_metadata_t::MAGIC,
                     detail::db_metadata_t::MAGIC_STRING_LEN)) {
            // Cannot make forward progress if we don't have writable maps
            MONAD_ASSERT(
                can_write_to_map,
                "First copy of metadata corrupted, but not opened for "
                "healing");
            // Overwrite the front copy with the backup copy
            detail::db_copy(
                db_metadata_[0].main, db_metadata_[1].main, map_size);
        }
    }

    // Version mismatch check
    constexpr unsigned magic_version_len = 3;
    constexpr unsigned magic_prefix_len =
        detail::db_metadata_t::MAGIC_STRING_LEN - magic_version_len;
    if (0 == memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata_t::MAGIC,
                 magic_prefix_len) &&
        memcmp(
            db_metadata_[0].main->magic + magic_prefix_len,
            detail::db_metadata_t::MAGIC + magic_prefix_len,
            magic_version_len)) {
        MONAD_ABORT_PRINTF(
            "DB was generated with version %s. The current code base is on "
            "version %s. Please regenerate with the new DB version.",
            db_metadata_[0].main->magic,
            detail::db_metadata_t::MAGIC);
    }

    // Magic string matched, replace any dirty copy with the non-dirty copy
    if (0 == memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata_t::MAGIC,
                 detail::db_metadata_t::MAGIC_STRING_LEN) &&
        0 == memcmp(
                 db_metadata_[1].main->magic,
                 detail::db_metadata_t::MAGIC,
                 detail::db_metadata_t::MAGIC_STRING_LEN)) {
        if (can_write_to_map) {
            MONAD_ASSERT(
                !db_metadata_[0].main->is_dirty().load(
                    std::memory_order_acquire) ||
                    !db_metadata_[1].main->is_dirty().load(
                        std::memory_order_acquire),
                "Both copies of metadata are dirty, this is unexpected and "
                "indicates a bug in the code");
            // Replace the dirty copy with the non-dirty copy
            if (db_metadata_[0].main->is_dirty().load(
                    std::memory_order_acquire)) {
                detail::db_copy(
                    db_metadata_[0].main, db_metadata_[1].main, map_size);
            }
            else if (db_metadata_[1].main->is_dirty().load(
                         std::memory_order_acquire)) {
                detail::db_copy(
                    db_metadata_[1].main, db_metadata_[0].main, map_size);
            }
        }
        else {
            if (db_metadata_[0].main->is_dirty().load(
                    std::memory_order_acquire) ||
                db_metadata_[1].main->is_dirty().load(
                    std::memory_order_acquire)) {

                // Wait a bit to see if they clear before complaining
                bool dirty;
                auto const begin = std::chrono::steady_clock::now();
                do {
                    dirty = db_metadata_[0].main->is_dirty().load(
                                std::memory_order_acquire) ||
                            db_metadata_[1].main->is_dirty().load(
                                std::memory_order_acquire);
                    std::this_thread::yield();
                }
                while (dirty && (std::chrono::steady_clock::now() - begin <
                                 std::chrono::seconds(1)));

                /* If after one second a dirty bit remains set, and we don't
                have writable maps, can't forward progress.
                */
                MONAD_ASSERT(
                    !dirty,
                    "DB metadata was closed dirty, but not opened for "
                    "healing");
            }
        }
    }

    map_root_offsets_();

    // config db_metadata chunk list if mismatched
    if (0 != memcmp(
                 db_metadata_[0].main->magic,
                 detail::db_metadata_t::MAGIC,
                 detail::db_metadata_t::MAGIC_STRING_LEN)) {
        MONAD_ASSERT(
            can_write_to_map,
            "Neither copy of the DB metadata is valid, and not opened for "
            "writing so stopping now.");
        for (uint32_t n = 0; n < chunk_count; n++) {
            MONAD_ASSERT(
                chunk_bytes_used(n) == 0,
                "DB metadata is invalid, but storage pool has non-empty "
                "chunks. This is unexpected and indicates a bug in the "
                "code.");
        }
        // Work on the first copy, and copy it to the second at the end

        // clear the db_metadata map size range
        memset(db_metadata_[0].main, 0, map_size);
        // chunk_count fits within 20 bits
        MONAD_DEBUG_ASSERT((chunk_count & ~0xfffffU) == 0);
        db_metadata_[0].main->chunk_info_count = chunk_count & 0xfffffU;

        // reset the chunk lists
        memset(
            &db_metadata_[0].main->free_list,
            0xff,
            sizeof(db_metadata_[0].main->free_list));
        memset(
            &db_metadata_[0].main->fast_list,
            0xff,
            sizeof(db_metadata_[0].main->fast_list));
        memset(
            &db_metadata_[0].main->slow_list,
            0xff,
            sizeof(db_metadata_[0].main->slow_list));
        auto *chunk_info =
            start_lifetime_as_array<detail::db_metadata_t::chunk_info_t>(
                db_metadata_[0].main->chunk_info, chunk_count);
        for (size_t n = 0; n < chunk_count; n++) {
            auto &ci = chunk_info[n];
            ci.prev_chunk_id = ci.next_chunk_id =
                detail::db_metadata_t::chunk_info_t::INVALID_CHUNK_ID;
        }

        // magics are not set yet, so memcpy is fine here
        memcpy(db_metadata_[1].main, db_metadata_[0].main, map_size);

        // Insert first two chunks to fast and slow list respectively
        auto const fast_offset = chunk_offset(0);
        append(DbStorage::chunk_list::fast, fast_offset.id);
        MONAD_ASSERT(
            db_metadata()->fast_list.begin == db_metadata()->fast_list.end);
        MONAD_ASSERT(db_metadata()->fast_list_begin()->insertion_count() == 0);

        auto const slow_offset = chunk_offset(1);
        append(DbStorage::chunk_list::slow, slow_offset.id);
        MONAD_ASSERT(
            db_metadata()->fast_list.begin == db_metadata()->fast_list.end);
        MONAD_ASSERT(db_metadata()->slow_list_begin()->insertion_count() == 0);

        // insert the rest of the chunks to free list
        for (uint32_t id = 2; id < chunk_count; ++id) {
            append(DbStorage::chunk_list::free, id);
            MONAD_ASSERT(db_metadata()->at(id)->index(db_metadata()) == id);
        }

        advance_db_offsets_to(fast_offset, slow_offset);

        // TODO: put these to an opaque struct
        set_latest_finalized_version(INVALID_BLOCK_NUM);
        set_latest_verified_version(INVALID_BLOCK_NUM);
        set_latest_voted(INVALID_BLOCK_NUM, bytes32_t{});
        // set_auto_expire_version_metadata(0);
        // init history length to the capacity by default
        set_history_length(db_metadata_[0].root_offsets.size());

        for (auto const i : {0, 1}) {
            auto *const m = db_metadata_[i].main;
            auto g = m->hold_dirty();
            memset(
                m->future_variables_unused,
                0xff,
                sizeof(m->future_variables_unused));
        }

        // zero out root offsets on both copies
        for (auto const i : {0, 1}) {
            auto root_offsets = db_metadata_[i].root_offsets;
            memset(
                (unsigned char *)root_offsets.data(),
                0,
                root_offsets.size_bytes());
        }
        // Set magic strings, mark as done
        std::atomic_signal_fence(
            std::memory_order_seq_cst); // no reordering here
        for (auto const i : {0, 1}) {
            memcpy(
                db_metadata_[i].main->magic,
                detail::db_metadata_t::MAGIC,
                detail::db_metadata_t::MAGIC_STRING_LEN);
        }
    }
    else { // resume from an existing db and underlying storage
        if (!is_read_only_) {
            // Destroy any contents after wip offsets
            rewind_to_match_offsets();
        }
    }
}

bool DbStorage::try_trim_contents_after(chunk_offset_t const)
{
    // TODO: implement this
    return true;
}

void DbStorage::destroy_contents(uint32_t const)
{
    // TODO: implement this
}

void DbStorage::rewind_to_match_offsets()
{
    auto const fast_offset = db_metadata()->db_offsets.start_of_wip_offset_fast;
    MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
    auto const slow_offset = db_metadata()->db_offsets.start_of_wip_offset_slow;
    MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);
    // TODO: fast/slow list offsets should always be greater than last
    // written root offset. Free all chunks after fast_offset.id Free all
    // chunks after fast_offset.id
    auto const *ci = db_metadata()->at(fast_offset.id);
    while (ci != db_metadata()->fast_list_end()) {
        auto const idx = db_metadata()->fast_list.end;
        remove(idx);
        destroy_contents(idx);
        append(chunk_list::free, idx);
    }
    MONAD_ASSERT(try_trim_contents_after(fast_offset));

    // Same for slow list
    auto const *slow_ci = db_metadata()->at(slow_offset.id);
    while (slow_ci != db_metadata()->slow_list_end()) {
        auto const idx = db_metadata()->slow_list.end;
        remove(idx);
        destroy_contents(idx);
        append(chunk_list::free, idx);
    }
    MONAD_ASSERT(try_trim_contents_after(slow_offset));
}

// both copies are mapped to the chunk immediately following the db_metadata
// chunk.
void DbStorage::map_root_offsets_()
{
    // Map in the DB version history storage
    // Firstly reserve address space for each copy
    constexpr unsigned root_offsets_chunk_count = 2;

    size_t const map_bytes_per_chunk = chunk_capacity / 2;
    size_t const db_version_history_storage_bytes =
        map_bytes_per_chunk * root_offsets_chunk_count;

    std::byte *reservation[2]; // 2 copies
    reservation[0] = (std::byte *)::mmap(
        nullptr,
        db_version_history_storage_bytes,
        PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
        -1,
        0);
    MONAD_ASSERT(reservation[0] != MAP_FAILED);
    reservation[1] = (std::byte *)::mmap(
        nullptr,
        db_version_history_storage_bytes,
        PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
        -1,
        0);
    MONAD_ASSERT(reservation[1] != MAP_FAILED);

    // For each chunk, map the first half into the first copy and the
    // second half into the second copy
    for (size_t n = 0; n < root_offsets_chunk_count; n++) {
        auto const start_offset =
            root_offsets_ring_buffer_offset().raw() + n * chunk_capacity;
        file_mmap_helper_(
            map_bytes_per_chunk,
            start_offset,
            reservation[0] + n * map_bytes_per_chunk,
            MAP_FIXED);
        file_mmap_helper_(
            map_bytes_per_chunk,
            start_offset + map_bytes_per_chunk,
            reservation[1] + n * map_bytes_per_chunk,
            MAP_FIXED);
    }
    auto const root_offsets_capacity =
        db_version_history_storage_bytes / sizeof(chunk_offset_t);
    db_metadata_[0].root_offsets = {
        start_lifetime_as<chunk_offset_t>((chunk_offset_t *)reservation[0]),
        root_offsets_capacity};
    db_metadata_[1].root_offsets = {
        start_lifetime_as<chunk_offset_t>((chunk_offset_t *)reservation[1]),
        root_offsets_capacity};
}

MONAD_STORAGE_NAMESPACE_END
