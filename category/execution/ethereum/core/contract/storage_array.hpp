#pragma once

#include <category/execution/ethereum/core/contract/storage_variable.hpp>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

// An array in the State trie. First index is the size.
template <typename T>
    requires std::is_trivially_copyable_v<T>
class StorageArray
{
    State &state_;
    Address const &address_;
    StorageVariable<u64_be> length_;
    uint256_t const start_index_;

    static constexpr size_t SLOT_PER_ELEM = StorageVariable<T>::N;

public:
    StorageArray(State &state, Address const &address, bytes32_t const &slot)
        : state_{state}
        , address_{address}
        , length_{StorageVariable<u64_be>(state, address, slot)}
        , start_index_{intx::be::load<uint256_t>(slot) + 1}
    {
    }

    uint64_t length() const noexcept
    {
        uint64_t const len = length_.load().native();
        if (MONAD_UNLIKELY(len == 0)) {
            return 0;
        }
        return len;
    }

    bool empty() const noexcept
    {
        return length() == 0;
    }

    StorageVariable<T> get(uint64_t const index) const noexcept
    {
        uint256_t const offset = start_index_ + index * SLOT_PER_ELEM;
        return StorageVariable<T>{
            state_, address_, intx::be::store<bytes32_t>(offset)};
    }

    void push(T const &value) noexcept
    {
        auto const len = length();
        uint256_t const offset = start_index_ + len * SLOT_PER_ELEM;
        StorageVariable<T> var{
            state_, address_, intx::be::store<bytes32_t>(offset)};
        var.store(value);
        length_.store(len + 1);
    }

    T pop() noexcept
    {
        T value{};
        auto len = length();
        if (MONAD_LIKELY(len > 0)) {
            len = len - 1;
            auto var = get(len);
            value = var.clear();
            length_.store(len);
        }
        return value;
    }
};

MONAD_NAMESPACE_END
