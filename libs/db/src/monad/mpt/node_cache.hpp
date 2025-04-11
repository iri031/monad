#pragma once

#include <monad/core/assert.h>
#include <monad/lru/static_lru_cache.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/util.hpp>

#include <cstddef>

MONAD_MPT_NAMESPACE_BEGIN

class NodeCache
{
    size_t const max_mem_;
    static_lru_cache<
        chunk_offset_t, std::shared_ptr<Node>, chunk_offset_t_hasher>
        cache_;
    size_t current_mem_;

public:
    static constexpr size_t AVERAGE_NODE_SIZE = 100;

    using Key = chunk_offset_t;
    using Value = std::shared_ptr<Node>;
    using ConstAccessor = static_lru_cache<
        chunk_offset_t, std::shared_ptr<Node>,
        chunk_offset_t_hasher>::ConstAccessor;

    explicit NodeCache(size_t const max_mem)
        : max_mem_(max_mem)
        , cache_(
              max_mem / AVERAGE_NODE_SIZE, chunk_offset_t::invalid_value(), {})
        , current_mem_{0}
    {
    }

    void
    insert(chunk_offset_t const &key, std::shared_ptr<Node> nvalue) noexcept
    {
        size_t const bytes_being_added = nvalue ? (nvalue->get_mem_size()) : 0;
        auto const pvalue = cache_.insert(key, std::move(nvalue));
        size_t const bytes_being_removed =
            pvalue ? (pvalue->get_mem_size()) : 0;
        MONAD_ASSERT(
            bytes_being_removed <= bytes_being_added ||
            (bytes_being_removed - bytes_being_added) <= current_mem_);
        current_mem_ += (bytes_being_added - bytes_being_removed);
        if (current_mem_ > max_mem_) {
            cache_.trim_oldest(
                [&](auto const &i) {
                    if (current_mem_ <= max_mem_) {
                        return false;
                    }
                    if (i.val) {
                        current_mem_ -= i.val->get_mem_size();
                    }
                    return true;
                },
                chunk_offset_t::invalid_value(),
                {});
        }
    }

    bool find(ConstAccessor &acc, Key const &key) noexcept
    {
        return cache_.find(acc, key);
    }

    size_t size() const noexcept
    {
        return cache_.size();
    }

    size_t memory() const noexcept
    {
        return current_mem_;
    }

    void clear() noexcept
    {
        cache_.clear();
        current_mem_ = 0;
    }
};

MONAD_MPT_NAMESPACE_END
