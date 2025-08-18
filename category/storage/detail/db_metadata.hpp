#pragma once

#include <category/core/bytes.hpp>
#include <category/core/start_lifetime_as_polyfill.hpp>
#include <category/storage/config.hpp>
#include <category/storage/detail/unsigned_20.hpp>
#include <category/storage/util.hpp>

#include <atomic>
#include <cstdint>

MONAD_STORAGE_NAMESPACE_BEGIN

class DbStorage;

namespace detail
{
    struct db_metadata_t;
#ifndef __clang__
    constexpr bool bitfield_layout_check()
    {
        /* Make sure reserved0_ definitely lives at offset +3
         */
        constexpr struct
        {
            uint32_t chunk_info_count : 20;
            uint32_t unused0_ : 4;
            uint32_t reserved0_ : 8;
        } v{.reserved0_ = 1};

        struct type
        {
            uint8_t x[sizeof(v)];
        };

        constexpr type ret = std::bit_cast<type>(v);
        return ret.x[sizeof(v) - 1]; // last byte
    }
#endif

    inline void
    db_copy(db_metadata_t *dest, db_metadata_t const *src, size_t bytes);

    /* We have two categories of metadata:
    - Synced: dependent data is guaranteed durable on disk.
    - Unsynced: dependent data may still only live in memory, and can be lost on
crash/kill. */
    struct db_metadata_t
    {
        friend class MONAD_STORAGE_NAMESPACE::DbStorage;
        friend inline void
        db_copy(db_metadata_t *dest, db_metadata_t const *src, size_t bytes);

        static constexpr char const *MAGIC = "MONAD000";
        static constexpr unsigned MAGIC_STRING_LEN = 8;

        char magic[MAGIC_STRING_LEN];

        uint32_t chunk_info_count : 20; // items in chunk_info below
        // The above two fields determine the size of the db_metadata
        uint32_t unused0_ : 4; // next item MUST be on a byte boundary
        uint32_t reserved_for_is_dirty_ : 8; // for is_dirty below
        // DO NOT INSERT ANYTHING IN HERE
        uint64_t capacity_in_free_list; // used to detect when free space is
                                        // running low

        uint64_t version_lower_bound_;
        uint64_t next_version_;

        // Starting here are 0xff initialized bytes

        /* NOTE Remember to update the DB restore implementation in the CLI
        tool if you modify anything after this! */
        // cannot use atomic_uint64_t here because db_metadata_t has to be
        // trivially copyable for db_copy().
        uint64_t history_length;
        uint64_t history_length_synced;
        int64_t auto_expire_version;

        // TODO: move those execution related metadata into an opaque type
        uint64_t latest_finalized_version;
        uint64_t latest_verified_version;
        uint64_t latest_finalized_version_synced;
        uint64_t latest_verified_version_synced;
        // unsynced info, gets cleared after restart
        uint64_t latest_voted_version;
        bytes32_t latest_voted_block_id; // 32 bytes

        // padding for adding future atomics without requiring DB reset
        uint8_t future_variables_unused[4096];

        struct db_offsets_info_t
        {
            // starting offsets of current wip db block's contents. all
            // data contents written pass this point are not yet validated, and
            // should be rewound if restart.
            chunk_offset_t start_of_wip_offset_fast;
            chunk_offset_t start_of_wip_offset_slow;

            db_offsets_info_t() = delete;
            db_offsets_info_t(db_offsets_info_t const &) = delete;
            db_offsets_info_t(db_offsets_info_t &&) = delete;
            db_offsets_info_t &operator=(db_offsets_info_t const &) =
                default; // purely to please the compiler
            db_offsets_info_t &operator=(db_offsets_info_t &&) = delete;
            ~db_offsets_info_t() = default;

            constexpr db_offsets_info_t(
                chunk_offset_t start_of_wip_offset_fast_,
                chunk_offset_t start_of_wip_offset_slow_)
                : start_of_wip_offset_fast(start_of_wip_offset_fast_)
                , start_of_wip_offset_slow(start_of_wip_offset_slow_)
            {
            }

            void store(db_offsets_info_t const &o)
            {
                start_of_wip_offset_fast = o.start_of_wip_offset_fast;
                start_of_wip_offset_slow = o.start_of_wip_offset_slow;
            }
        } db_offsets;

        struct version_ring_buffer_info_t
        {
            uint64_t version_lower_bound_;
            uint64_t next_version_; // all bits zero turns into INVALID_VERSION
        } version_ring_buffer;

        size_t total_size() const noexcept
        {
            return sizeof(db_metadata_t) +
                   chunk_info_count * sizeof(chunk_info_t);
        }

        // used to know if the metadata was being
        // updated when the process suddenly exited
        std::atomic<uint8_t> &is_dirty() noexcept
        {
            static_assert(sizeof(std::atomic<uint8_t>) == sizeof(uint8_t));
#ifndef __clang__
            static_assert(bitfield_layout_check());
#endif
            return *start_lifetime_as<std::atomic<uint8_t>>(
                (std::byte *)&capacity_in_free_list - 1);
        }

        struct id_pair
        {
            uint32_t begin, end;
        } free_list, fast_list, slow_list;

        struct chunk_info_t
        {
            static constexpr uint32_t INVALID_CHUNK_ID = 0xfffff;

            // chunk list managment related fields
            uint64_t prev_chunk_id : 20; // same bits as from chunk_offset_t
            uint64_t in_fast_list : 1;
            uint64_t in_slow_list : 1;
            uint64_t insertion_count0_ : 10; // align next to 8 bit boundary
                                             // to aid codegen
            uint64_t next_chunk_id : 20; // same bits as from chunk_offset_t
            uint64_t unused0_ : 2;
            uint64_t insertion_count1_ : 10;

            uint32_t index(db_metadata_t const *parent) const noexcept
            {
                auto ret = uint32_t(this - parent->chunk_info);
                MONAD_DEBUG_ASSERT(ret < parent->chunk_info_count);
                return ret;
            }

            unsigned_20 insertion_count() const noexcept
            {
                return uint32_t(insertion_count1_ << 10) |
                       uint32_t(insertion_count0_);
            }

            chunk_info_t const *prev(db_metadata_t const *parent) const noexcept
            {
                if (prev_chunk_id == INVALID_CHUNK_ID) {
                    return nullptr;
                }
                MONAD_DEBUG_ASSERT(prev_chunk_id < parent->chunk_info_count);
                return &parent->chunk_info[prev_chunk_id];
            }

            chunk_info_t const *next(db_metadata_t const *parent) const noexcept
            {
                if (next_chunk_id == INVALID_CHUNK_ID) {
                    return nullptr;
                }
                MONAD_DEBUG_ASSERT(next_chunk_id < parent->chunk_info_count);
                return &parent->chunk_info[next_chunk_id];
            }
        };
#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wc99-extensions"
#elif defined __GNUC__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wpedantic"
#endif
        chunk_info_t chunk_info[];
#ifdef __clang__
    #pragma clang diagnostic pop
#elif defined __GNUC__
    #pragma GCC diagnostic pop
#endif
        static_assert(sizeof(chunk_info_t) == 8);
        static_assert(std::is_trivially_copyable_v<chunk_info_t>);

        auto hold_dirty() noexcept
        {
            static_assert(sizeof(std::atomic<uint8_t>) == sizeof(uint8_t));

            struct holder_t
            {
                db_metadata_t *parent;

                explicit holder_t(db_metadata_t *p)
                    : parent(p)
                {
                    parent->is_dirty().store(1, std::memory_order_release);
                }

                holder_t(holder_t const &) = delete;

                holder_t(holder_t &&o) noexcept
                    : parent(o.parent)
                {
                    o.parent = nullptr;
                }

                ~holder_t()
                {
                    if (parent != nullptr) {
                        parent->is_dirty().store(0, std::memory_order_release);
                    }
                }
            };

            return holder_t(this);
        }

        chunk_info_t const *at(uint32_t idx) const noexcept
        {
            MONAD_DEBUG_ASSERT(idx < chunk_info_count);
            return &chunk_info[idx];
        }

        chunk_info_t atomic_load_chunk_info(
            uint32_t const idx, std::memory_order load_ord =
                                    std::memory_order_seq_cst) const noexcept
        {
            return reinterpret_cast<std::atomic<chunk_info_t> const *>(at(idx))
                ->load(load_ord);
        }

        chunk_info_t const &operator[](uint32_t idx) const noexcept
        {
            MONAD_DEBUG_ASSERT(idx < chunk_info_count);
            return chunk_info[idx];
        }

        chunk_info_t const *free_list_begin() const noexcept
        {
            if (free_list.begin == UINT32_MAX) {
                return nullptr;
            }
            MONAD_DEBUG_ASSERT(free_list.begin < chunk_info_count);
            return &chunk_info[free_list.begin];
        }

        chunk_info_t const *free_list_end() const noexcept
        {
            if (free_list.end == UINT32_MAX) {
                return nullptr;
            }
            MONAD_DEBUG_ASSERT(free_list.end < chunk_info_count);
            return &chunk_info[free_list.end];
        }

        chunk_info_t const *fast_list_begin() const noexcept
        {
            if (fast_list.begin == UINT32_MAX) {
                return nullptr;
            }
            MONAD_DEBUG_ASSERT(fast_list.begin < chunk_info_count);
            return &chunk_info[fast_list.begin];
        }

        chunk_info_t const *fast_list_end() const noexcept
        {
            if (fast_list.end == UINT32_MAX) {
                return nullptr;
            }
            MONAD_DEBUG_ASSERT(fast_list.end < chunk_info_count);
            return &chunk_info[fast_list.end];
        }

        chunk_info_t const *slow_list_begin() const noexcept
        {
            if (slow_list.begin == UINT32_MAX) {
                return nullptr;
            }
            MONAD_DEBUG_ASSERT(slow_list.begin < chunk_info_count);
            return &chunk_info[slow_list.begin];
        }

        chunk_info_t const *slow_list_end() const noexcept
        {
            if (slow_list.end == UINT32_MAX) {
                return nullptr;
            }
            MONAD_DEBUG_ASSERT(slow_list.end < chunk_info_count);
            return &chunk_info[slow_list.end];
        }

    private:
        chunk_info_t *at_(uint32_t idx) noexcept
        {
            MONAD_DEBUG_ASSERT(idx < chunk_info_count);
            return &chunk_info[idx];
        }

        // TODO: remove the unnecessary atomic operation
        void append_(id_pair &list, chunk_info_t *i) noexcept
        {
            // Insertion count is assigned to chunk_info_t *i atomically
            auto g = hold_dirty();
            chunk_info_t info;
            info.in_fast_list = (&list == &fast_list);
            info.in_slow_list = (&list == &slow_list);
            info.insertion_count0_ = info.insertion_count1_ = 0;
            info.next_chunk_id = chunk_info_t::INVALID_CHUNK_ID;
            if (list.end == UINT32_MAX) {
                MONAD_DEBUG_ASSERT(list.begin == UINT32_MAX);
                info.prev_chunk_id = chunk_info_t::INVALID_CHUNK_ID;
                list.begin = list.end = i->index(this);
            }
            else {
                MONAD_DEBUG_ASSERT((list.end & ~0xfffffU) == 0);
                info.prev_chunk_id = list.end & 0xfffffU;
                auto *tail = at_(list.end);
                auto const insertion_count = tail->insertion_count() + 1;
                MONAD_DEBUG_ASSERT(
                    tail->next_chunk_id == chunk_info_t::INVALID_CHUNK_ID);
                info.insertion_count0_ = uint32_t(insertion_count) & 0x3ff;
                info.insertion_count1_ =
                    uint32_t(insertion_count >> 10) & 0x3ff;
                list.end = tail->next_chunk_id = i->index(this) & 0xfffffU;
            }
            reinterpret_cast<std::atomic<chunk_info_t> *>(i)->store(
                info, std::memory_order_release);
        }

        void remove_(chunk_info_t *i) noexcept
        {
            auto get_list = [&]() -> id_pair & {
                if (i->in_fast_list) {
                    return fast_list;
                }
                if (i->in_slow_list) {
                    return slow_list;
                }
                return free_list;
            };
            auto g = hold_dirty();
            if (i->prev_chunk_id == chunk_info_t::INVALID_CHUNK_ID &&
                i->next_chunk_id == chunk_info_t::INVALID_CHUNK_ID) {
                id_pair &list = get_list();
                MONAD_DEBUG_ASSERT(list.begin == i->index(this));
                MONAD_DEBUG_ASSERT(list.end == i->index(this));
                list.begin = list.end = UINT32_MAX;
#ifndef NDEBUG
                i->in_fast_list = i->in_slow_list = false;
#endif
                return;
            }
            if (i->prev_chunk_id == chunk_info_t::INVALID_CHUNK_ID) {
                id_pair &list = get_list();
                MONAD_DEBUG_ASSERT(list.begin == i->index(this));
                auto *next = at_(i->next_chunk_id);
                next->prev_chunk_id = chunk_info_t::INVALID_CHUNK_ID;
                list.begin = next->index(this);
#ifndef NDEBUG
                i->in_fast_list = i->in_slow_list = false;
                i->next_chunk_id = chunk_info_t::INVALID_CHUNK_ID;
#endif
                return;
            }
            if (i->next_chunk_id == chunk_info_t::INVALID_CHUNK_ID) {
                id_pair &list = get_list();
                MONAD_DEBUG_ASSERT(list.end == i->index(this));
                auto *prev = at_(i->prev_chunk_id);
                prev->next_chunk_id = chunk_info_t::INVALID_CHUNK_ID;
                list.end = prev->index(this);
#ifndef NDEBUG
                i->in_fast_list = i->in_slow_list = false;
                i->prev_chunk_id = chunk_info_t::INVALID_CHUNK_ID;
#endif
                return;
            }
            MONAD_ASSERT(
                "remove_() has had mid-list removals explicitly disabled "
                "to prevent insertion count becoming inaccurate" == nullptr);
            auto *prev = at_(i->prev_chunk_id);
            auto *next = at_(i->next_chunk_id);
            prev->next_chunk_id = next->index(this) & 0xfffffU;
            next->prev_chunk_id = prev->index(this) & 0xfffffU;
#ifndef NDEBUG
            i->in_fast_list = i->in_slow_list = false;
            i->prev_chunk_id = i->next_chunk_id =
                chunk_info_t::INVALID_CHUNK_ID;
#endif
        }

        void free_capacity_add_(uint64_t bytes) noexcept
        {
            auto g = hold_dirty();
            capacity_in_free_list += bytes;
        }

        void free_capacity_sub_(uint64_t bytes) noexcept
        {
            auto g = hold_dirty();
            capacity_in_free_list -= bytes;
        }

        void advance_db_offsets_to_(
            db_offsets_info_t const &offsets_to_apply) noexcept
        {
            auto g = hold_dirty();
            db_offsets.store(offsets_to_apply);
        }
    };

    static_assert(sizeof(db_metadata_t) == 4288);
    static_assert(std::is_trivially_copyable_v<db_metadata_t>);

    /* A dirty bit setting memcpy implementation, so the dirty bit gets held
high during the memory copy.
*/
    inline void
    db_copy(db_metadata_t *dest, db_metadata_t const *src, size_t bytes)
    {
        alignas(db_metadata_t) std::byte buffer[sizeof(db_metadata_t)];
        memcpy(buffer, src, sizeof(db_metadata_t));
        auto *intr = start_lifetime_as<db_metadata_t>(buffer);
        MONAD_ASSERT(intr->is_dirty().load(std::memory_order_acquire) == false);
        auto g1 = intr->hold_dirty();
        auto g2 = dest->hold_dirty();
        dest->next_version_ = 0; // INVALID_VERSION
        auto const old_next_version = intr->next_version_;
        intr->next_version_ = 0; // INVALID_VERSION
        memcpy((void *)dest, buffer, sizeof(db_metadata_t));
        memcpy(
            ((std::byte *)dest) + sizeof(db_metadata_t),
            ((std::byte const *)src) + sizeof(db_metadata_t),
            bytes - sizeof(db_metadata_t));
        std::atomic_ref<uint64_t>(dest->next_version_)
            .store(old_next_version, std::memory_order_release);
    };
}

MONAD_STORAGE_NAMESPACE_END
