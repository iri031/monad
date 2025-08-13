#pragma once

#include <category/core/assert.h>
#include <category/storage/config.hpp>
#include <category/storage/detail/db_metadata.hpp>

#include <cstdint>
#include <filesystem>

MONAD_STORAGE_NAMESPACE_BEGIN

class DbStorage
{
    bool is_read_only_, is_read_only_allow_dirty_, is_newly_truncated_;
    int fd_;

    enum class type_t_ : uint8_t
    {
        unknown,
        file,
        block_device
    } device_type_;

    size_t size_of_device_;
    uint64_t unique_hash_;

    unsigned char *chunks_data_;

    // Chunk metadata is stored at the end of the file / block device
    struct chunk_metadata_t
    {
        // Reserving the end of chunks, 1 chunk for db_metadata, 2 for root
        // offsets
        static constexpr unsigned reserved_chunks = 3;
        static constexpr char const *MAGIC = "MND0";
        static constexpr unsigned MAGIC_STRING_LEN = 4;
        // Preceding this is an array of uint32_t of chunk bytes used

        uint32_t spare_[13]; // set aside for flags later
        uint32_t config_hash; // hash of this configuration
        uint8_t magic[4]; // "MND0" for v1 of this metadata

        static size_t
        num_chunks(file_offset_t const end_of_this_offset) noexcept
        {
            auto ret = end_of_this_offset / (chunk_capacity + sizeof(uint32_t));
            // We need the front CPU_PAGE_SIZE of this metadata to not
            // include any chunk
            auto endofchunks =
                round_down_align<CPU_PAGE_BITS>(ret * chunk_capacity);
            auto startofmetadata = round_down_align<CPU_PAGE_BITS>(
                end_of_this_offset - ret * sizeof(uint32_t));
            if (startofmetadata == endofchunks) {
                return ret - 1;
            }
            return ret - reserved_chunks; // last few chunks are reserved for
                                          // db_metadata and root offsets
        }

        // Bytes used by the pool metadata on this device
        static size_t
        total_size(file_offset_t const end_of_this_offset) noexcept
        {
            auto const count = num_chunks(end_of_this_offset);
            return sizeof(chunk_metadata_t) + count * sizeof(uint32_t);
        }

        std::span<std::atomic<uint32_t>>
        chunk_bytes_used(file_offset_t end_of_this_offset) const noexcept
        {
            static_assert(sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));
            auto const count = num_chunks(end_of_this_offset);
            return {
                start_lifetime_as_array<std::atomic<uint32_t>>(
                    const_cast<std::byte *>(
                        reinterpret_cast<std::byte const *>(this)) -
                        count * sizeof(uint32_t),
                    count),
                count};
        }

    } *chunk_metadata_; // mmapped address

    static_assert(sizeof(chunk_metadata_t) == 60);

    // db metadata and root offsets are stored in the last few reserved
    // chunks
    struct DbMetadata
    {
        detail::db_metadata_t *main{nullptr};
        std::span<chunk_offset_t> root_offsets;
    } db_metadata_[2]; // mmapped addresses

    void db_copy(DbMetadata &dest, DbMetadata const &src, size_t main_map_size);

    void rewind_to_match_offsets();

    void try_trim_chunk_content_after(chunk_offset_t offset);

    void destroy_contents(uint32_t id)
    {
        try_trim_chunk_content_after({id, 0});
    }

    chunk_offset_t db_metadata_map_offset() const noexcept
    {
        MONAD_ASSERT(num_chunks() < std::numeric_limits<uint32_t>::max());
        return chunk_offset((uint32_t)num_chunks());
    }

    chunk_offset_t root_offsets_map_offset() const noexcept
    {
        MONAD_ASSERT(num_chunks() + 1 < std::numeric_limits<uint32_t>::max());
        return chunk_offset((uint32_t)num_chunks() + 1);
    }

public:
    // 256Mb hardcoded chunk size
    static constexpr uint32_t chunk_capacity = 1UL << 28;

    //! \brief What to do when opening the pool for use.
    enum class Mode
    {
        open_existing,
        create_if_needed,
        truncate
    };

    struct creation_flags
    {
        //! Whether to open the database read-only
        uint32_t open_read_only : 1;
        //! Whether to open the database read-only allowing a dirty closed
        //! database
        uint32_t open_read_only_allow_dirty : 1;
        //! Whether to use madvise(MADV_RANDOM) on the mmaped chunk data
        uint32_t madv_random_access : 1;

        constexpr creation_flags()
            : open_read_only(false)
            , open_read_only_allow_dirty(false)
            , madv_random_access(true)
        {
        }
    };

    enum class chunk_list : uint8_t
    {
        free = 0,
        fast = 1,
        slow = 2
    };

public:
    DbStorage(std::filesystem::path path, Mode mode, creation_flags flags = {});

    DbStorage(use_anonymous_inode_tag, off_t len);

    ~DbStorage();

    chunk_offset_t chunk_offset(uint32_t const id) const noexcept
    {
        return {id, 0};
    }

    // TODO: maybe expose read and write api to access chunk data instead of
    // direct memory access (where the impl does boundary check)
    unsigned char const *get_data(chunk_offset_t const offset) const noexcept
    {
        MONAD_ASSERT(!is_read_only());
        MONAD_ASSERT(
            offset.id < num_chunks(), "cannot access out of range data");
        return chunks_data_ + offset.raw();
    }

    unsigned char *get_data(chunk_offset_t const offset) noexcept
    {
        MONAD_ASSERT(
            offset.id < num_chunks(), "cannot access out of range data");
        return chunks_data_ + offset.raw();
    }

    size_t num_chunks() const noexcept
    {
        return chunk_metadata_->num_chunks(file_offset_t(size_of_device_));
    }

    uint32_t chunk_bytes_used(uint32_t const id) const noexcept
    {
        MONAD_ASSERT(id < num_chunks());
        return chunk_metadata_->chunk_bytes_used(size_of_device_)[id];
    }

    void
    advance_chunk_bytes_used(uint32_t const id, unsigned const bytes) noexcept
    {
        MONAD_ASSERT(!is_read_only());
        MONAD_ASSERT(id < num_chunks());
        auto chunk_bytes_used =
            chunk_metadata_->chunk_bytes_used(size_of_device_);
        MONAD_ASSERT_PRINTF(
            chunk_bytes_used[id] + bytes <= chunk_capacity,
            "advancing chunk %u bytes used by %u would exceed chunk capacity "
            "%u",
            id,
            bytes,
            chunk_capacity);
        chunk_bytes_used[id] += bytes;
    }

    detail::db_metadata_t const *db_metadata() const noexcept
    {
        return db_metadata_[0].main;
    }

    //! \brief True if the storage pool was opened read only
    bool is_read_only() const noexcept
    {
        return is_read_only_;
    }

    //! \brief True if the storage pool was opened read only but a dirty closed
    //! state is to be allowed
    bool is_read_only_allow_dirty() const noexcept
    {
        return is_read_only_allow_dirty_;
    }

    //! \brief True if the storage pool was just truncated, and structures may
    //! need reinitialising
    bool is_newly_truncated() const noexcept
    {
        return is_newly_truncated_;
    }

    auto root_offsets(unsigned const which = 0) const
    {
        class root_offsets_delegator
        {
            std::atomic_ref<uint64_t> version_lower_bound_;
            std::atomic_ref<uint64_t> next_version_;
            std::span<chunk_offset_t> root_offsets_chunks_;

            void
            update_version_lower_bound_(uint64_t lower_bound = uint64_t(-1))
            {
                auto const version_lower_bound =
                    version_lower_bound_.load(std::memory_order_acquire);
                auto idx = (lower_bound < version_lower_bound)
                               ? lower_bound
                               : version_lower_bound;
                auto const max_version =
                    next_version_.load(std::memory_order_acquire) - 1;
                while (idx < max_version && (*this)[idx] == INVALID_OFFSET) {
                    idx++;
                }
                if (idx != version_lower_bound) {
                    version_lower_bound_.store(idx, std::memory_order_release);
                }
            }

        public:
            explicit root_offsets_delegator(DbMetadata const &m)
                : version_lower_bound_(m.main->version_lower_bound_)
                , next_version_(m.main->next_version_)
                , root_offsets_chunks_(m.root_offsets)
            {
                MONAD_DEBUG_ASSERT(
                    root_offsets_chunks_.size() ==
                    1ULL
                        << (63 -
                            std::countl_zero(root_offsets_chunks_.size())));
            }

            size_t capacity() const noexcept
            {
                return root_offsets_chunks_.size();
            }

            void push(chunk_offset_t const o) noexcept
            {
                auto const wp = next_version_.load(std::memory_order_relaxed);
                auto const next_wp = wp + 1;
                MONAD_ASSERT(next_wp != 0);
                auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &root_offsets_chunks_
                        [wp & (root_offsets_chunks_.size() - 1)]);
                p->store(o, std::memory_order_release);
                next_version_.store(next_wp, std::memory_order_release);
                if (o != INVALID_OFFSET) {
                    update_version_lower_bound_();
                }
            }

            void assign(size_t const i, chunk_offset_t const o) noexcept
            {
                auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &root_offsets_chunks_
                        [i & (root_offsets_chunks_.size() - 1)]);
                p->store(o, std::memory_order_release);
                update_version_lower_bound_(
                    (o != INVALID_OFFSET) ? i : uint64_t(-1));
            }

            chunk_offset_t operator[](size_t const i) const noexcept
            {
                return start_lifetime_as<std::atomic<chunk_offset_t> const>(
                           &root_offsets_chunks_
                               [i & (root_offsets_chunks_.size() - 1)])
                    ->load(std::memory_order_acquire);
            }

            // return INVALID_VERSION indicates that db is empty
            uint64_t max_version() const noexcept
            {
                auto const wp = next_version_.load(std::memory_order_acquire);
                return wp - 1;
            }

            void reset_all(uint64_t const version)
            {
                version_lower_bound_.store(0, std::memory_order_release);
                next_version_.store(0, std::memory_order_release);
                memset(
                    (void *)root_offsets_chunks_.data(),
                    0xff,
                    root_offsets_chunks_.size() * sizeof(chunk_offset_t));
                version_lower_bound_.store(version, std::memory_order_release);
                next_version_.store(version, std::memory_order_release);
            }

            void rewind_to_version(uint64_t const version)
            {
                MONAD_ASSERT(version < max_version());
                MONAD_ASSERT(max_version() - version <= capacity());
                for (uint64_t i = version + 1; i <= max_version(); i++) {
                    assign(i, INVALID_OFFSET);
                }
                if (version <
                    version_lower_bound_.load(std::memory_order_acquire)) {
                    version_lower_bound_.store(
                        version, std::memory_order_release);
                }
                next_version_.store(version + 1, std::memory_order_release);
                update_version_lower_bound_();
            }
        };

        return root_offsets_delegator{db_metadata_[which]};
    }

    ////////////////////////////////////////////////
    /// Db metadata functions
    ////////////////////////////////////////////////
    void apply_to_both_main_copies(auto &&f) noexcept
    {
        MONAD_ASSERT(!is_read_only());
        f(db_metadata_[0].main);
        f(db_metadata_[1].main);
    }

    void append(chunk_list list, uint32_t idx) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
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
            if (list == chunk_list::free) {
                MONAD_DEBUG_ASSERT(chunk_bytes_used(idx) == 0);
                m->free_capacity_add_(chunk_capacity);
            }
        };
        apply_to_both_main_copies(f);
    }

    void remove(uint32_t const idx) noexcept
    {
        bool const is_free_list =
            (!db_metadata()->at(idx)->in_fast_list &&
             !db_metadata()->at(idx)->in_slow_list);
        auto f = [&](detail::db_metadata_t *m) {
            m->remove_(m->at_(idx));
            if (is_free_list) {
                MONAD_DEBUG_ASSERT(chunk_bytes_used(idx) == 0);
                m->free_capacity_sub_(chunk_capacity);
            }
        };
        apply_to_both_main_copies(f);
    }

    void advance_db_offsets_to(
        chunk_offset_t const fast_offset,
        chunk_offset_t const slow_offset) noexcept
    {
        // To detect bugs in replacing fast/slow node writer to the wrong chunk
        // list
        MONAD_ASSERT(db_metadata()->at(fast_offset.id)->in_fast_list);
        MONAD_ASSERT(db_metadata()->at(slow_offset.id)->in_slow_list);
        apply_to_both_main_copies([&](detail::db_metadata_t *m) {
            m->advance_db_offsets_to_(detail::db_metadata_t::db_offsets_info_t{
                fast_offset, slow_offset});
        });
    }

    void append_root_offset(chunk_offset_t const root_offset) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            root_offsets(m == db_metadata_[1].main).push(root_offset);
        };
        apply_to_both_main_copies(f);
    }

    void update_root_offset(
        size_t const i, chunk_offset_t const root_offset) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            root_offsets(m == db_metadata_[1].main).assign(i, root_offset);
        };
        apply_to_both_main_copies(f);
    }

    void fast_forward_next_version(uint64_t const new_version) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            auto ro = root_offsets(m == db_metadata_[1].main);
            uint64_t curr_version = ro.max_version();
            MONAD_ASSERT(
                curr_version == INVALID_VERSION || new_version > curr_version);

            if (curr_version == INVALID_VERSION ||
                new_version - curr_version >= ro.capacity()) {
                ro.reset_all(new_version);
            }
            else {
                while (curr_version + 1 < new_version) {
                    ro.push(INVALID_OFFSET);
                    curr_version = ro.max_version();
                }
            }
        };
        apply_to_both_main_copies(f);
    }

    void set_latest_finalized_version(uint64_t const version) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            reinterpret_cast<std::atomic_uint64_t *>(
                &m->latest_finalized_version)
                ->store(version, std::memory_order_release);
        };
        apply_to_both_main_copies(f);
    }

    void set_latest_verified_version(uint64_t const version) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            reinterpret_cast<std::atomic_uint64_t *>(
                &m->latest_verified_version)
                ->store(version, std::memory_order_release);
        };
        apply_to_both_main_copies(f);
    }

    void
    set_latest_voted(uint64_t const version, bytes32_t const &block_id) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            reinterpret_cast<std::atomic_uint64_t *>(&m->latest_voted_version)
                ->store(version, std::memory_order_release);
            m->latest_voted_block_id = block_id;
        };
        apply_to_both_main_copies(f);
    }

    void set_history_length(uint64_t const history_len) noexcept
    {
        auto f = [&](detail::db_metadata_t *m) {
            auto g = m->hold_dirty();
            auto const ro = root_offsets(m == db_metadata_[1].main);
            MONAD_ASSERT(history_len > 0 && history_len <= ro.capacity());
            reinterpret_cast<std::atomic_uint64_t *>(&m->history_length)
                ->store(history_len, std::memory_order_relaxed);
        };
        apply_to_both_main_copies(f);
    }

    uint64_t db_history_max_version() const noexcept
    {
        return root_offsets().max_version();
    }

    uint64_t db_history_min_valid_version() const noexcept
    {
        auto const offsets = root_offsets();
        auto min_version = db_history_range_lower_bound();
        for (; min_version != offsets.max_version(); ++min_version) {
            if (offsets[min_version] != INVALID_OFFSET) {
                break;
            }
        }
        return min_version;
    }

    uint64_t db_history_range_lower_bound() const noexcept
    {
        auto const max_version = db_history_max_version();
        if (max_version == INVALID_VERSION) {
            return INVALID_VERSION;
        }
        else {
            auto const history_range_min =
                max_version >= version_history_length()
                    ? (max_version - version_history_length() + 1)
                    : 0;
            auto const ro_version_lower_bound =
                db_metadata()->version_lower_bound_;
            MONAD_ASSERT(ro_version_lower_bound >= history_range_min);
            return ro_version_lower_bound;
        }
    }

    uint64_t version_history_length() const noexcept
    {
        return start_lifetime_as<std::atomic_uint64_t const>(
                   &db_metadata()->history_length)
            ->load(std::memory_order_relaxed);
    }

    chunk_offset_t
    get_root_offset_at_version(uint64_t const version) const noexcept
    {
        if (version <= db_history_max_version()) {
            auto const offset = root_offsets()[version];
            if (version >= db_history_range_lower_bound()) {
                return offset;
            }
        }
        return INVALID_OFFSET;
    }

private:
    void init_(int const fd, Mode mode, creation_flags flags = {});
    void verify_and_map_chunk_metadata_(Mode op);
    uint32_t compute_config_hash_();
    void init_db_metadata_();
    void map_root_offsets_();
    // deduce flag and mode based on opening flags
    void *file_mmap_helper_(
        size_t size, file_offset_t offset, void *map_address,
        int additional_flags);
};

MONAD_STORAGE_NAMESPACE_END
