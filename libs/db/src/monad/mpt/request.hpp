#pragma once

#include <monad/core/nibble.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <bit>
#include <cstdint>
#include <optional>

MONAD_MPT_NAMESPACE_BEGIN

struct Requests
{
    uint16_t mask{0};
    uint8_t prefix_len{0};
    UpdateList sublists[16];
    std::optional<Update> opt_leaf{std::nullopt};

    Requests() = default;

    UpdateList const &operator[](size_t i) const & noexcept
    {
        MONAD_DEBUG_ASSERT(i < 16);
        return sublists[i];
    }

    UpdateList &&operator[](size_t i) && noexcept
    {
        MONAD_DEBUG_ASSERT(i < 16);
        return std::move(sublists[i]);
    }

    constexpr unsigned char get_first_branch() const noexcept
    {
        MONAD_DEBUG_ASSERT(mask);
        return static_cast<unsigned char>(std::countr_zero(mask));
    }

    constexpr UpdateList &&first_and_only_list() && noexcept
    {
        MONAD_DEBUG_ASSERT(std::popcount(mask) == 1);
        return std::move(sublists[get_first_branch()]);
    }

    constexpr NibblesView get_first_path() const noexcept
    {
        return sublists[get_first_branch()].front().key;
    }

    constexpr void reset(unsigned const prefix_index) noexcept
    {
        mask = 0;
        opt_leaf = std::nullopt;
        MONAD_DEBUG_ASSERT(prefix_index <= std::numeric_limits<uint8_t>::max());
        prefix_len = static_cast<uint8_t>(prefix_index);
    }

    // clang-format: off
    // return the number of sublists it splits into, equals #distinct_nibbles
    // at prefix index i.
    // - if single update, prefix_index != key.size() * 2, put to one of
    //   sublists, n = 1
    // - if single update, prefix_index == key.size() * 2, set
    //   opt_leaf, n = 0
    // - if multiple updates, prefix_index = one of key size, set
    //   opt_leaf, split the rest to sublists, n >= 1
    // clang-format: on
    unsigned
    split_into_sublists(UpdateList &&updates, unsigned const prefix_index)
    {
        reset(prefix_index);
        unsigned n = 0;
        while (!updates.empty()) {
            Update &req = updates.front();
            MONAD_ASSERT(req.key.nibble_size() != 0);
            updates.pop_front();
            if (prefix_index == req.key.nibble_size()) {
                opt_leaf = std::move(req);
                continue;
            }
            auto const branch = req.key.get(prefix_index);
            if (sublists[branch].empty()) {
                mask |= uint16_t(1u << branch);
                ++n;
            }
            sublists[branch].push_front(req);
        }
        return n;
    }
};

static_assert(sizeof(Requests) == 352);
static_assert(alignof(Requests) == 8);

MONAD_MPT_NAMESPACE_END
