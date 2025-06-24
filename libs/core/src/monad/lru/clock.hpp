#pragma once

#include "monad/config.hpp"
#include <monad/core/assert.h>

#include <tbb/concurrent_hash_map.h>

#include <algorithm>
#include <atomic>
#include <memory>
#include <optional>

#include <monad/util/concurrentqueue.h>

MONAD_NAMESPACE_BEGIN

/**
 * A thread-safe FIFO/CLOCK/n-th chance balancing frequency & recency models
 * with promotion & demotion to ordered FIFO queue of cold/hot stages. based on:
 * https://dl.acm.org/doi/pdf/10.1145/3600006.3613147
 * It is intended that allocation is performed once on initialisation to a fixed
 * size and a low overhead cache hit access path and hit ratios similar to LRU
 *
 * note: cache size + queue sizes are unreliable as they over/under-flow
 * during multithreaded access by a small percentage
 **/

template <typename Key, typename Value>
struct ClockFrame
{
    Key key;
    Value val;
    std::atomic<uint8_t> ref_bit_;

    ClockFrame()
        : ref_bit_(0) {};

    ClockFrame(Key k, Value v)
        : key(std::move(k))
        , val(std::move(v))
        , ref_bit_(0)
    {
    }

    ~ClockFrame() = default;

    uint8_t get_ref_count() const
    {
        return ref_bit_.load(std::memory_order_acquire);
    }

    void reset_ref_count()
    {
        ref_bit_.store(0);
    }

    void increment_ref()
    {
        if (ref_bit_.load(std::memory_order_relaxed) < 3) {
            ref_bit_.fetch_add(1, std::memory_order_relaxed);
        }
    }

    void decrement_ref()
    {
        if (ref_bit_.load(std::memory_order_relaxed) != 0) {
            ref_bit_.fetch_sub(1, std::memory_order_relaxed);
        }
    }

    bool can_evict() const
    {
        if (ref_bit_.load(std::memory_order_relaxed) == 0) {
            return true;
        }
        return false;
    }
};

template <
    typename Key, typename Value,
    typename KeyHashCompare = tbb::tbb_hash_compare<Key>>
class ClockReplacer
{
public:
    using Frame = ClockFrame<Key, Value>;
    using FramePtr = std::shared_ptr<Frame>;
    using HashMap = tbb::concurrent_hash_map<Key, FramePtr, KeyHashCompare>;

    using ConstAccessor = typename HashMap::const_accessor;
    using Accessor = typename HashMap::accessor;

    HashMap hmap_;
    std::size_t cache_cap_;

    // main/hot queue
    ::moodycamel::ConcurrentQueue<FramePtr> hot_;
    std::size_t hot_cap_;

    // cold queue
    ::moodycamel::ConcurrentQueue<FramePtr> cold_;
    std::size_t cold_cap_;

    // ghost or frequency dictionary
    HashMap ghost_;
    std::size_t ghost_cap_;

    // config parameters
    static constexpr uint8_t REF_COUNT = 3;
    static constexpr uint8_t HOT_RATIO = 90;

    explicit ClockReplacer(std::size_t cache_size)
        : hmap_(cache_size)
        , cache_cap_(cache_size)
        , hot_cap_(cache_size * HOT_RATIO / 100)
        , ghost_(cache_size)
        , ghost_cap_(cache_size)
    {
        cold_cap_ = cache_size - hot_cap_;

        MONAD_ASSERT_PRINTF(
            hot_cap_ + cold_cap_ == cache_size,
            "fifo hot/cold queue mismatch: %lu %lu %lu",
            hot_cap_,
            cold_cap_,
            cache_size);
    }

    ~ClockReplacer()
    {
        clear();
    };

    std::optional<std::reference_wrapper<Value>> find(Key const &key)
    {
        ConstAccessor acc;

        if (!hmap_.find(acc, key)) {
            return std::nullopt;
        }

        auto frame = acc->second;
        acc.release();
        frame->increment_ref();

        return std::ref(frame->val);
    }

    void insert(Key const &key, Value const &value) noexcept
    {
        if (ConstAccessor acc; hmap_.find(acc, key)) {
            auto frame = acc->second;
            frame->val = value;
            frame->increment_ref();
            return;
        }

        while (hmap_.size() >= cache_cap_) {
            if (cold_.size_approx() >= cold_cap_) {
                evict_cold();
            }
            else {
                evict_hot();
            }
        }

        auto frame = std::make_shared<Frame>(key, value);
        ConstAccessor const_acc;

        if (Accessor acc; ghost_.find(const_acc, key)) {
            ghost_.erase(acc);
            acc.release();

            hot_.enqueue(frame);
        }
        else {
            cold_.enqueue(frame);
        }

        if (Accessor acc; hmap_.insert(acc, key)) {
            acc->second = frame;
            acc.release();
        }
    };

    void clear() noexcept
    {
        FramePtr empty;
        while (hot_.try_dequeue(empty) && cold_.try_dequeue(empty)) {
        }

        hmap_.clear();
        ghost_.clear();
    }

    std::size_t size() const noexcept
    {
        return hmap_.size();
    }

private:
    void evict_cold() noexcept
    {
        FramePtr victim;

        while (cold_.try_dequeue(victim)) {
            // 'one-hit wonder' filter
            if (victim->get_ref_count() > 1) {
                victim->reset_ref_count();
                if (!hot_.enqueue(std::move(victim))) {
                    {
                        evict_hot();
                        hot_.enqueue(std::move(victim));
                    }
                }
            }
            else {
                if (Accessor acc; hmap_.find(acc, victim->key)) {
                    hmap_.erase(acc);
                    acc.release();
                }

                add_to_ghost(victim->key);

                break;
            }
        }
    }

    void evict_hot() noexcept
    {
        FramePtr victim;

        while (hot_.try_dequeue(victim)) {
            if (victim->get_ref_count() > 0) {
                victim->decrement_ref();
                hot_.enqueue(victim);
            }
            else {
                if (Accessor acc; hmap_.find(acc, victim->key)) {
                    hmap_.erase(acc);
                    acc.release();
                }

                break;
            }
        }
    }

    void add_to_ghost(Key const &key)
    {
        if (ConstAccessor acc; ghost_.size() < ghost_cap_) {
            ghost_.insert(acc, key);
        }
    }
};

MONAD_NAMESPACE_END
