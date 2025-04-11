#pragma once

#include <monad/config.hpp>
#include <monad/core/unordered_map.hpp>

#include <boost/intrusive/list.hpp>

#include <vector>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

// An LRU cache with a fixed max size. Calls to `find()` will not allocate.
template <
    typename Key, typename Value,
    typename Hash = ankerl::unordered_dense::hash<Key>>
class static_lru_cache
{
    struct list_node
        : public boost::intrusive::list_base_hook<
              boost::intrusive::link_mode<boost::intrusive::normal_link>>
    {
        Key key;
        Value val;
    };

    using List = boost::intrusive::list<list_node>;
    using ListIter = typename List::iterator;
    using Map = ankerl::unordered_dense::segmented_map<Key, ListIter, Hash>;

    std::vector<list_node> array_;
    boost::intrusive::list<list_node>
        list_; // ordering, always same size as storage
    Map map_; // lookup, but also current valid items

public:
    using ConstAccessor = Map::const_iterator;

    explicit static_lru_cache(
        size_t const size, Key const &key = Key(), Value const &value = Value())
        : array_(size, list_node{.key = key, .val = value})
    {
        for (size_t i = 0; i < size; ++i) {
            list_.push_back(array_[i]);
        }
        map_.reserve(size);
    }

    ~static_lru_cache() = default;

    // `value` on exit is the former value.
    Value insert(Key const &key, Value value) noexcept
    {
        using std::swap;
        {
            auto it = map_.find(key);
            if (it != map_.end()) {
                swap(it->second->val, value);
                update_lru(it->second);
                return value;
            }
        }
        auto it = std::prev(list_.end());
        map_.erase(it->key);
        list_.erase(it);

        // Reuse node
        it->key = key;
        swap(it->val, value);

        list_.insert(list_.begin(), *it);
        map_[key] = it;
        return value;
    }

    bool find(ConstAccessor &acc, Key const &key) noexcept
    {
        acc = map_.find(key);
        if (acc == map_.end()) {
            return false;
        }
        update_lru(acc->second);
        return true;
    }

    size_t size() const noexcept
    {
        return map_.size();
    }

    void clear() noexcept
    {
        map_.clear();
    }

    // Call invocable on oldest member first. Return true to trim. Returning
    // false exits early.
    template <class F>
        requires(std::is_invocable_r_v<bool, F, list_node const &>)
    void
    trim_oldest(F &&f, Key const &key = Key(), Value const &value = Value())
    {
        size_t const empty_end_slots = list_.size() - map_.size();
        auto it = list_.rbegin();
        std::advance(it, empty_end_slots);
        for (; it != list_.rend(); ++it) {
            if (!f(*it)) {
                break;
            }
            map_.erase(it->key);
            it->key = key;
            it->val = value;
        }
    }

private:
    void update_lru(ListIter it)
    {
        list_.splice(list_.begin(), list_, it);
    }
};

MONAD_NAMESPACE_END
