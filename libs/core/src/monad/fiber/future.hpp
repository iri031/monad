#pragma once

#include <atomic>
#include <bit>
#include <cstring>
#include <exception>
#include <future>
#include <source_location>
#include <string_view>
#include <system_error>

#include <monad/core/srcloc.hpp>
#include <monad/fiber/config.hpp>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/fiber_semaphore.h>

MONAD_FIBER_NAMESPACE_BEGIN

template <typename T>
class simple_promise;

/// Stripped-down future class that is used with simple_promise; see the
/// simple_promise documentation for details
template <typename T>
class simple_future
{
public:
    simple_future() noexcept;
    simple_future(simple_future const &other) = delete;
    simple_future(simple_future &&) noexcept;

    T get();

    bool valid() const noexcept;
    void wait();
    bool poll() noexcept;

    simple_future &operator=(simple_future const &) = delete;
    simple_future &operator=(simple_future &&) noexcept;

private:
    friend class simple_promise<T>;
    simple_future(monad_fiber_channel_t *);

    monad_fiber_channel_t *channel_;
    monad_fiber_vbuf_t *vbuf_;
};

/**
 * Implementation of a limited promise/future interface using
 * monad_fiber_channel_t, to ease our transition away from the future/promise
 * API abstraction.
 *
 * Unlike std::promise, this does not perform any dynamic memory allocation.
 * The memory for the channel is provided by the promise itself, which means the
 * simple_future cannot detect if has been abandoned.
 *
 * Consequently, the user must make sure the simple_promise object will outlive
 * the simple_future. Once the promise's lifetime ends, trying to use the future
 * will result in undefined behavior. Specifically, we cannot detect the
 * equivalent of std::future_errc::broken_promise and in this situation an
 * invalid memory read would occur.
 *
 * For this reason, the future and promise are called "simple" because although
 * the methods have the same names as their std:: equivalents, they are more
 * efficient but less powerful. Any features we don't need yet, e.g., setting
 * and rethrowing exceptions, is also not implemented.
 *
 * \tparam T type of the object stored within the promise
 */
template <typename T>
class simple_promise
{
public:
    simple_promise(
        std::source_location const & = std::source_location::current());
    simple_promise(simple_promise const &) = delete;
    simple_promise(simple_promise &&) noexcept;
    ~simple_promise() = default;

    simple_future<T> get_future();

    void set_value(T const &);

    void set_value(T &&);

    std::errc set_debug_name(std::string_view);

    simple_promise &operator=(simple_promise const &) = delete;
    simple_promise &operator=(simple_promise &&) noexcept;

private:
    static constexpr bool using_vbuf_inplace =
        sizeof(T) <= MONAD_FIBER_VBUF_MAX_INTERNAL;

    bool contains_value() const
    {
        return false; // XXX: solve the TOCTOU somehow
    }

    T *get_value_buffer() const;

    monad_fiber_channel_t channel_;
    monad_fiber_vbuf_t vbuf_;
    [[no_unique_address]] alignas(
        T) std::byte buffer_[using_vbuf_inplace ? 0 : sizeof(T)];
};

/*
 * Specializations
 */

template <>
class simple_future<void>
{
public:
    simple_future() noexcept;
    simple_future(simple_future const &other) = delete;
    simple_future(simple_future &&) noexcept;

    void get();

    bool valid() const noexcept;
    void wait();
    bool poll() noexcept;

    simple_future &operator=(simple_future const &) = delete;
    simple_future &operator=(simple_future &&) noexcept;

private:
    friend class simple_promise<void>;
    simple_future(monad_fiber_semaphore_t *);

    monad_fiber_semaphore_t *sem_;
    bool has_token_;
};

template <>
class simple_promise<void>
{
public:
    simple_promise(
        std::source_location const & = std::source_location::current());
    simple_promise(simple_promise const &) = delete;
    simple_promise(simple_promise &&) noexcept;
    ~simple_promise() = default;

    simple_future<void> get_future();

    void set_value();

    std::errc set_debug_name(std::string_view);

    simple_promise &operator=(simple_promise const &) = delete;
    simple_promise &operator=(simple_promise &&) noexcept;

private:
    bool contains_value() const;

    monad_fiber_semaphore_t sem_;
};

/*
 * Implementation
 */

template <typename T>
simple_future<T>::simple_future() noexcept
    : simple_future{nullptr}
{
}

template <typename T>
simple_future<T>::simple_future(simple_future &&other) noexcept
    : simple_future{}
{
    std::swap(channel_, other.channel_);
    std::swap(vbuf_, other.vbuf_);
}

template <typename T>
simple_future<T>::simple_future(monad_fiber_channel_t *channel)
    : channel_{channel}
    , vbuf_{nullptr}
{
}

template <typename T>
T simple_future<T>::get()
{
    if (vbuf_ == nullptr) {
        wait();
    }
    T *const t = std::bit_cast<T *>(monad_fiber_vbuf_data(vbuf_).iov_base);
    vbuf_ = nullptr; // Don't allow it to be used again
    return std::move(*t);
}

template <typename T>
bool simple_future<T>::valid() const noexcept
{
    return vbuf_ != nullptr;
}

template <typename T>
void simple_future<T>::wait()
{
    if (channel_ == nullptr) {
        throw std::future_error{std::future_errc::no_state};
    }
    if (vbuf_ != nullptr) {
        throw std::future_error{std::future_errc::future_already_retrieved};
    }
    vbuf_ = monad_fiber_channel_pop(channel_, MONAD_FIBER_PRIO_NO_CHANGE);
}

template <typename T>
bool simple_future<T>::poll() noexcept
{
    vbuf_ = monad_fiber_channel_try_pop(channel_);
    return valid();
}

inline simple_future<void>::simple_future() noexcept
    : sem_{nullptr}
    , has_token_{false}
{
}

inline simple_future<void>::simple_future(simple_future &&other) noexcept
    : simple_future{}
{
    std::swap(sem_, other.sem_);
    std::swap(has_token_, other.has_token_);
}

inline simple_future<void>::simple_future(monad_fiber_semaphore_t *sem)
    : sem_{sem}
    , has_token_{false}
{
}

inline void simple_future<void>::get()
{
    if (!has_token_) {
        wait();
    }
    has_token_ = false;
}

inline bool simple_future<void>::valid() const noexcept
{
    return has_token_;
}

inline void simple_future<void>::wait()
{
    if (sem_ == nullptr) {
        throw std::future_error{std::future_errc::no_state};
    }
    if (has_token_) {
        throw std::future_error{std::future_errc::future_already_retrieved};
    }
    monad_fiber_semaphore_wait(sem_, MONAD_FIBER_PRIO_NO_CHANGE);
}

inline bool simple_future<void>::poll() noexcept
{
    has_token_ = monad_fiber_semaphore_try_consume(sem_);
    return valid();
}

template <typename T>
simple_promise<T>::simple_promise(std::source_location const &s)
{
    iovec ext_buf = {.iov_base = buffer_, .iov_len = sizeof buffer_};
    monad_fiber_channel_init(&channel_, make_srcloc(s));
    monad_fiber_vbuf_init(&vbuf_, using_vbuf_inplace ? nullptr : &ext_buf);
}

template <typename T>
simple_promise<T>::simple_promise(simple_promise &&other) noexcept
    : simple_promise{}
{
    MONAD_SPINLOCK_LOCK(&other.channel_.lock);
    // Copy the bits for the vbuf
    std::memcpy(&vbuf_, &other.vbuf_, sizeof vbuf_);
    if (!TAILQ_EMPTY(&other.channel_.ready_vbufs)) {
        // This vbuf (or rather, the original copy of it) was linked into
        // the ready list of 'other'. Push it in onto our channel instead.
        monad_fiber_channel_push(&channel_, &vbuf_);
    }

    // It may not be enough to copy the vbuf bits, we may need to run a
    // move constructor
    if constexpr (
        using_vbuf_inplace && !std::is_trivially_move_constructible_v<T>) {
        new (get_value_buffer()) T{std::move(*other.get_value_buffer())};
    }

    // Steal the old list of waiting fibers
    TAILQ_CONCAT(
        &channel_.wait_queue.waiting_fibers,
        &other.channel_.wait_queue.waiting_fibers,
        wait_link);
    monad_spinlock_unlock(&other.channel_.lock);
}

template <typename T>
simple_future<T> simple_promise<T>::get_future()
{
    return simple_future<T>{&channel_};
}

template <typename T>
void simple_promise<T>::set_value(T const &value)
{
    if (contains_value()) {
        throw std::future_error{std::future_errc::promise_already_satisfied};
    }
    new (get_value_buffer()) T{value};
    monad_fiber_channel_push(&channel_, &vbuf_);
}

template <typename T>
void simple_promise<T>::set_value(T &&value)
{
    if (contains_value()) {
        throw std::future_error{std::future_errc::promise_already_satisfied};
    }
    new (get_value_buffer()) T{std::move(value)};
    monad_fiber_channel_push(&channel_, &vbuf_);
}

template <typename T>
std::errc simple_promise<T>::set_debug_name(std::string_view sv)
{
    return static_cast<std::errc>(
        monad_fiber_channel_set_name(&channel_, sv.data()));
}

template <typename T>
simple_promise<T> &simple_promise<T>::operator=(simple_promise &&other) noexcept
{
    return *new (this) simple_promise{std::move(other)};
}

template <typename T>
T *simple_promise<T>::get_value_buffer() const
{
    if constexpr (using_vbuf_inplace) {
        return std::bit_cast<T *>(&vbuf_.in_place[0]);
    }
    else {
        return std::bit_cast<T *>(buffer_);
    }
}

inline simple_promise<void>::simple_promise(std::source_location const &s)
{
    monad_fiber_semaphore_init(&sem_, make_srcloc(s));
}

inline simple_promise<void>::simple_promise(simple_promise &&other) noexcept
    : simple_promise{}
{
    MONAD_SPINLOCK_LOCK(&other.sem_.lock);
    sem_.tokens = other.sem_.tokens;
    TAILQ_CONCAT(
        &sem_.wait_queue.waiting_fibers,
        &other.sem_.wait_queue.waiting_fibers,
        wait_link);
    monad_spinlock_unlock(&other.sem_.lock);
}

inline simple_future<void> simple_promise<void>::get_future()
{
    return simple_future<void>{&sem_};
}

inline void simple_promise<void>::set_value()
{
    std::atomic_ref<unsigned> const atomic_tokens{sem_.tokens};
    if (atomic_tokens > 0) {
        throw std::future_error{std::future_errc::promise_already_satisfied};
    }
    monad_fiber_semaphore_signal(&sem_);
}

inline std::errc simple_promise<void>::set_debug_name(std::string_view sv)
{
    return static_cast<std::errc>(
        monad_fiber_semaphore_set_name(&sem_, sv.data()));
}

inline simple_promise<void> &
simple_promise<void>::operator=(simple_promise &&other) noexcept
{
    return *new (this) simple_promise{std::move(other)};
}

MONAD_FIBER_NAMESPACE_END
