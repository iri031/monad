#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <intx/intx.hpp>

#include <optional>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

template <typename T>
    requires std::is_trivially_copyable_v<T>
class StorageVariable
{
public:
    static constexpr size_t N =
        (sizeof(T) + sizeof(bytes32_t) - 1) / sizeof(bytes32_t);

    struct Adapter
    {
        union
        {
            struct
            {
                bytes32_t raw[N];

                constexpr bytes32_t &operator[](size_t const i) noexcept
                {
                    return raw[i];
                }

                constexpr bytes32_t const &
                operator[](size_t const i) const noexcept
                {
                    return raw[i];
                }

            } slots;

            T typed;
        };

        Adapter()
            : slots{}
        {
        }

        Adapter(T const &t)
            : slots{}
        {
            typed = t;
        }
    };

    State &state_;
    Address const &address_;
    uint256_t const offset_;

    void store_(Adapter const &adapter)
    {
        for (size_t i = 0; i < N; ++i) {
            state_.set_storage(
                address_,
                intx::be::store<bytes32_t>(offset_ + i),
                adapter.slots[i]);
        }
    }

public:
    StorageVariable(State &state, Address const &address, bytes32_t key)
        : state_{state}
        , address_{address}
        , offset_{intx::be::load<uint256_t>(key)}
    {
    }

    StorageVariable(State &state, Address const &address, uint256_t const key)
        : state_{state}
        , address_{address}
        , offset_{key}
    {
    }

    T load() const noexcept
    {
        Adapter value;
        for (size_t i = 0; i < N; ++i) {
            value.slots[i] = state_.get_storage(
                address_, intx::be::store<bytes32_t>(offset_ + i));
        }
        return value.typed;
    }

    std::optional<T> load_checked() const noexcept
    {
        Adapter value;
        bool has_data = false;
        for (size_t i = 0; i < N; ++i) {
            value.slots[i] = state_.get_storage(
                address_, intx::be::store<bytes32_t>(offset_ + i));
            has_data |= (value.slots[i] != bytes32_t{});
        }
        return has_data ? value.typed : std::optional<T>{};
    }

    void store(T const &value)
    {
        Adapter adapter(value);
        store_(adapter);
    }

    T clear()
    {
        Adapter adapter{};
        auto const res = load();
        store_(adapter);
        return res;
    }
};

MONAD_NAMESPACE_END
