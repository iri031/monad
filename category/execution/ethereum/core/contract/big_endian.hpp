#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <type_traits>

MONAD_NAMESPACE_BEGIN

#pragma once

// BigEndian is a strongly typed big endian wrapper. This is used primarily for
// writing to state, to allow for simple conversion to and from big endian.
template <typename T>
    requires(std::is_integral_v<T> || std::is_same_v<T, uint256_t>)
struct BigEndian
{
    unsigned char bytes[sizeof(T)];

    BigEndian() = default;

    BigEndian(T const &x) noexcept
    {
        intx::be::store(bytes, x);
    }

    explicit BigEndian(uint8_t const (&raw)[sizeof(T)]) noexcept
    {
        std::memcpy(bytes, raw, sizeof(BigEndian<T>));
    }

    bool operator==(BigEndian<T> const &other) const noexcept
    {
        return 0 == memcmp(this, &other, sizeof(BigEndian<T>));
    }

    T native() const noexcept
    {
        return intx::be::load<T>(bytes);
    }

    BigEndian<T> &operator=(T const &x) noexcept
    {
        intx::be::store(bytes, x);
        return *this;
    }
};

using u16_be = BigEndian<uint16_t>;
using u32_be = BigEndian<uint32_t>;
using u64_be = BigEndian<uint64_t>;
using u256_be = BigEndian<uint256_t>;
static_assert(sizeof(u16_be) == sizeof(uint16_t));
static_assert(sizeof(u32_be) == sizeof(uint32_t));
static_assert(sizeof(u64_be) == sizeof(uint64_t));
static_assert(sizeof(u256_be) == sizeof(uint256_t));

template <typename T>
struct is_big_endian_wrapper : std::false_type
{
};

template <>
struct is_big_endian_wrapper<uint8_t> : std::true_type
{
};

template <typename U>
struct is_big_endian_wrapper<BigEndian<U>> : std::true_type
{
};

template <typename T>
concept BigEndianType = is_big_endian_wrapper<T>::value;

MONAD_NAMESPACE_END
