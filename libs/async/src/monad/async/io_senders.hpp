#pragma once

#include <monad/async/io.hpp>

#include <array>
#include <chrono>
#include <variant>

MONAD_ASYNC_NAMESPACE_BEGIN

/*! \class read_single_buffer_sender
\brief A Sender which (possibly partially) fills a single **registered** buffer
of bytes read from an offset in a file.

To have `AsyncIO` set a suitable registered buffer, you should Connect this to
its Receiver using `AsyncIO::make_connected()`.
*/
class read_single_buffer_sender
{
public:
    using buffer_type = filled_read_buffer;
    using const_buffer_type = filled_read_buffer;
    using result_type = result<std::reference_wrapper<buffer_type>>;

    static constexpr operation_type my_operation_type = operation_type::read;
    static constexpr bool own_write_buffer = false;

private:
    chunk_offset_t offset_;
    buffer_type buffer_;

public:
    constexpr read_single_buffer_sender(
        chunk_offset_t offset, size_t bytes_to_read)
        : offset_(offset)
        , buffer_(bytes_to_read)
    {
    }

    constexpr read_single_buffer_sender(
        chunk_offset_t offset, buffer_type buffer)
        : offset_(offset)
        , buffer_(std::move(buffer))
    {
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffer_type const &buffer() const & noexcept
    {
        return buffer_;
    }

    constexpr buffer_type buffer() && noexcept
    {
        return std::move(buffer_);
    }

    void reset(chunk_offset_t offset, size_t bytes_to_read)
    {
        offset_ = offset;
        buffer_ = buffer_type(bytes_to_read);
    }

    void reset(chunk_offset_t offset, buffer_type buffer)
    {
        offset_ = offset;
        buffer_ = std::move(buffer);
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        if (!buffer_) {
            buffer_.set_read_buffer(
                io_state->executor()->get_read_buffer(buffer_.size()));
        }
        size_t bytes_transferred = io_state->executor()->submit_read_request(
            buffer_.to_mutable_span(), offset_, io_state);
        if (bytes_transferred != size_t(-1)) {
            // It completed early
            return make_status_code(
                sender_errc::initiation_immediately_completed,
                bytes_transferred);
        }
        return success();
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        buffer_.set_bytes_transferred(count);
        return success(std::ref(buffer_));
    }
};

static_assert(sizeof(read_single_buffer_sender) == 40);
static_assert(alignof(read_single_buffer_sender) == 8);
static_assert(sender<read_single_buffer_sender>);

/*! \class read_multiple_buffer_sender
\brief A Sender which (possibly partially) scatter fills one or more
**unregistered** buffers of bytes read from an offset in a file.

Unlike `read_single_buffer_sender`, this scatter reads into unregistered
buffers. You therefore should NOT use `AsyncIO::make_connected()`, in
fact if you try it will be a compile time error.

Instead simply `connect()` it as for a normal Sender-Receiver pair.
*/
class read_multiple_buffer_sender
{
    static constexpr size_t SMALL_BUFFERS_COUNT = 4;

public:
    using buffer_type = std::span<std::byte>;
    using const_buffer_type = std::span<std::byte const>;
    using buffers_type = std::span<buffer_type>;
    using const_buffers_type = std::span<const_buffer_type>;
    using result_type = result<buffers_type>;

    static constexpr operation_type my_operation_type =
        operation_type::read_scatter;
    static constexpr bool own_write_buffer = false;

private:
    chunk_offset_t offset_;
    buffers_type buffers_;
    std::variant<
        std::array<struct iovec, SMALL_BUFFERS_COUNT>,
        std::vector<struct iovec>>
        iovecs_;

public:
    constexpr read_multiple_buffer_sender(
        chunk_offset_t offset, buffers_type buffers)
        : offset_(offset)
        , buffers_(std::move(buffers))
    {
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffers_type buffers() const noexcept
    {
        return buffers_;
    }

    void reset(chunk_offset_t offset, buffers_type buffers)
    {
        offset_ = offset;
        buffers_ = std::move(buffers);
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        try {
            std::span<const struct iovec> iovecs;
            if (buffers_.size() <= SMALL_BUFFERS_COUNT) {
                std::array<struct iovec, SMALL_BUFFERS_COUNT> temp;
                {
                    size_t n = 0;
                    for (; n < buffers_.size(); n++) {
                        temp[n] = {
                            (char *)buffers_[n].data(), buffers_[n].size()};
                    }
                    // Without this, GCC complains in release builds :(
                    for (; n < temp.size(); n++) {
                        temp[n].iov_base = nullptr;
                        temp[n].iov_len = 0;
                    }
                }

                iovecs_ = std::move(temp);
                auto &v = std::get<0>(iovecs_);
                iovecs = v;
                iovecs = iovecs.subspan(0, buffers_.size());
            }
            else {
                std::vector<struct iovec> temp;
                temp.reserve(buffers_.size());
                for (size_t n = 0; n < buffers_.size(); n++) {
                    temp[n] = {(char *)buffers_[n].data(), buffers_[n].size()};
                }
                iovecs_ = std::move(temp);
                auto &v = std::get<1>(iovecs_);
                iovecs = v;
            }
            size_t bytes_transferred =
                io_state->executor()->submit_read_request(
                    iovecs, offset_, io_state);
            if (bytes_transferred != size_t(-1)) {
                // It completed early
                return make_status_code(
                    sender_errc::initiation_immediately_completed,
                    bytes_transferred);
            }
            return success();
        }
        catch (...) {
            return system_code_from_exception();
        }
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        for (size_t n = 0; n < buffers_.size(); n++) {
            if (buffers_[n].size() > count) {
                buffers_[n] = {buffers_[n].data(), count};
                buffers_ = buffers_.subspan(0, n + 1);
                break;
            }
            if (buffers_[n].size() == count) {
                buffers_ = buffers_.subspan(0, n + 1);
                break;
            }
            count -= buffers_[n].size();
        }
        return success(buffers_);
    }
};

static_assert(sizeof(read_multiple_buffer_sender) == 96);
static_assert(alignof(read_multiple_buffer_sender) == 8);
static_assert(sender<read_multiple_buffer_sender>);

/*! \class write_single_buffer_sender
\brief A Sender which (possibly partially) writes a single **registered** buffer
of bytes into an offset in a file.

To have `AsyncIO` set a suitable registered buffer, you should Connect this to
its Receiver using `AsyncIO::make_connected()`.

Writes are treated specially and separately to all other operations by
`AsyncIO`. They get their own, dedicated, io_uring instance exclusively used for
writes. The ring is always the size of the maximum number of write i/o buffers,
so it is never possible that initiating a write will find the submission queue
full. The write io_uring instance is exclusively addressed using
`IOSQE_IO_DRAIN` so every write submitted must complete before the next write
begins. A strict append-only sequential order is enforced so the storage only
ever sees a single append operation to existing content, and writes are never
ever out of order.

All this is done to reduce read-modify-write cycles by the storage thus reducing
flash wear, easing the load on the SSD's CPUs, and causing writes to be paced
to the speed of the SSD rather than flooding it with i/o. This especially
matters when the SSD runs out of SLC cache and write speed drops sixfold, we
need to substantially back off all i/o to let the SSD recover.
*/

class write_single_buffer_sender
{
public:
    using buffer_type = filled_write_buffer;
    using const_buffer_type = filled_write_buffer;
    using result_type = result<std::reference_wrapper<buffer_type>>;

    static constexpr operation_type my_operation_type = operation_type::write;
    static constexpr bool own_write_buffer = true;

private:
    chunk_offset_t offset_;
    buffer_type buffer_;
    std::byte *append_;

public:
    constexpr write_single_buffer_sender(
        chunk_offset_t offset, size_t bytes_to_write)
        : offset_(offset)
        , buffer_(bytes_to_write)
        , append_(const_cast<std::byte *>(buffer_.data()))
    {
    }

    constexpr write_single_buffer_sender(
        chunk_offset_t offset, buffer_type buffer)
        : offset_(offset)
        , buffer_(std::move(buffer))
        , append_(const_cast<std::byte *>(buffer.data()))
    {
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffer_type const &buffer() const & noexcept
    {
        return buffer_;
    }

    constexpr buffer_type buffer() && noexcept
    {
        return std::move(buffer_);
    }

    void reset(chunk_offset_t offset, size_t bytes_to_write)
    {
        offset_ = offset;
        buffer_ = buffer_type(bytes_to_write);
        append_ = const_cast<std::byte *>(buffer_.data());
    }

    void reset(chunk_offset_t offset, buffer_type buffer)
    {
        offset_ = offset;
        buffer_ = std::move(buffer);
        append_ = const_cast<std::byte *>(buffer_.data());
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        MONAD_DEBUG_ASSERT(!!buffer_);
        buffer_.set_bytes_transferred(size_t(append_ - buffer_.data()));
        io_state->executor()->submit_write_request(buffer_, offset_, io_state);
        return success();
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        if (!bytes_transferred) {
            fprintf(
                stderr,
                "ERROR: Write of %zu bytes to chunk %u offset %llu failed "
                "with "
                "error "
                "'%s'\n",
                buffer().size(),
                offset().id,
                file_offset_t(offset().offset),
                bytes_transferred.assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        buffer_.set_bytes_transferred(count);
        return std::ref(buffer_);
    }

    constexpr size_t written_buffer_bytes() const noexcept
    {
        MONAD_DEBUG_ASSERT(buffer_.data() <= append_);
        return static_cast<size_t>(append_ - buffer_.data());
    }

    constexpr size_t remaining_buffer_bytes() const noexcept
    {
        auto const *end = buffer_.data() + buffer_.size();
        MONAD_DEBUG_ASSERT(end >= append_);
        return static_cast<size_t>(end - append_);
    }

    constexpr std::byte *advance_buffer_append(size_t bytes) noexcept
    {
        if (bytes > remaining_buffer_bytes()) {
            return nullptr;
        }
        auto *ret = append_;
        append_ += bytes;
        return ret;
    }
};

static_assert(sizeof(write_single_buffer_sender) == 48);
static_assert(alignof(write_single_buffer_sender) == 8);
static_assert(sender<write_single_buffer_sender>);

class write_no_owning_buffer_sender
{
public:
    using buffer_type = filled_write_buffer;
    using const_buffer_type = filled_write_buffer;
    using result_type = result<std::reference_wrapper<buffer_type>>;

    static constexpr operation_type my_operation_type = operation_type::write;
    static constexpr bool own_write_buffer = false;

private:
    chunk_offset_t offset_;
    buffer_type &buffer_;
    std::byte *append_;

public:
    constexpr write_no_owning_buffer_sender(
        chunk_offset_t offset, buffer_type &buffer)
        : offset_(offset)
        , buffer_(buffer)
        , append_(const_cast<std::byte *>(buffer.data()))
    {
        MONAD_ASSERT((offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
    }

    constexpr chunk_offset_t offset() const noexcept
    {
        return offset_;
    }

    constexpr buffer_type const &buffer() const & noexcept
    {
        return buffer_;
    }

    constexpr buffer_type buffer() && noexcept
    {
        return std::move(buffer_);
    }

    void reset(chunk_offset_t, buffer_type)
    {
        MONAD_ASSERT(false);
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        MONAD_DEBUG_ASSERT(!!buffer_);
        auto const bytes_transferred = size_t(append_ - buffer_.data());
        MONAD_DEBUG_ASSERT((offset_.offset & (DISK_PAGE_SIZE - 1)) == 0);
        MONAD_DEBUG_ASSERT((bytes_transferred & (DISK_PAGE_SIZE - 1)) == 0);
        buffer_.set_bytes_transferred(bytes_transferred);
        io_state->executor()->submit_write_request(buffer_, offset_, io_state);
        return success();
    }

    result_type completed(
        erased_connected_operation *, result<size_t> bytes_transferred) noexcept
    {
        if (!bytes_transferred) {
            fprintf(
                stderr,
                "ERROR: Write of %zu bytes to chunk %u offset %llu failed "
                "with "
                "error "
                "'%s'\n",
                buffer().size(),
                offset().id,
                file_offset_t(offset().offset),
                bytes_transferred.assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto &&count, std::move(bytes_transferred));
        buffer_.set_bytes_transferred(count);
        return std::ref(buffer_);
    }

    constexpr size_t written_buffer_bytes() const noexcept
    {
        MONAD_DEBUG_ASSERT(buffer_.data() <= append_);
        return static_cast<size_t>(append_ - buffer_.data());
    }

    constexpr size_t remaining_buffer_bytes() const noexcept
    {
        auto const *end = buffer_.data() + buffer_.size();
        MONAD_DEBUG_ASSERT(end >= append_);
        return static_cast<size_t>(end - append_);
    }

    constexpr std::byte *advance_buffer_append(size_t bytes) noexcept
    {
        if (bytes > remaining_buffer_bytes()) {
            return nullptr;
        }
        auto *ret = append_;
        append_ += bytes;
        return ret;
    }
};

static_assert(sizeof(write_no_owning_buffer_sender) == 24);
static_assert(alignof(write_no_owning_buffer_sender) == 8);
static_assert(sender<write_no_owning_buffer_sender>);

/*! \class timed_delay_sender
\brief A Sender which completes after a delay. The delay can be measured by
system clock or by monotonic clock. The delay can be absolute or relative to
now.

```
Benchmarking timed_delay_sender with a non-zero timeout ...
   Did 1.45344e+06 completions per second
Benchmarking timed_delay_sender with a zero timeout ...
   Did 4.76564e+06 completions per second
```
*/
class timed_delay_sender
{
    AsyncIO::timed_invocation_state state_;

    template <class Rep, class Period>
    static __kernel_timespec
    to_timespec_(std::chrono::duration<Rep, Period> rel)
    {
        auto const ns =
            std::chrono::duration_cast<std::chrono::nanoseconds>(rel).count();
        return __kernel_timespec{ns / 1000000000, ns % 1000000000};
    }

    static __kernel_timespec
    to_timespec_(std::chrono::steady_clock::time_point dle)
    {
        auto const ns = std::chrono::duration_cast<std::chrono::nanoseconds>(
                            dle.time_since_epoch())
                            .count();
        return __kernel_timespec{ns / 1000000000, ns % 1000000000};
    }

    static __kernel_timespec
    to_timespec_(std::chrono::system_clock::time_point dle)
    {
        auto const ns = std::chrono::duration_cast<std::chrono::nanoseconds>(
                            dle.time_since_epoch())
                            .count();
        return __kernel_timespec{ns / 1000000000, ns % 1000000000};
    }

public:
    using result_type = result<void>;

    static constexpr operation_type my_operation_type = operation_type::timeout;
    static constexpr bool own_write_buffer = false;

public:
    //! Complete after the specified delay from now. WARNING: Uses a
    //! monotonic clock NOT invariant to sleep!
    template <class Rep, class Period>
    explicit constexpr timed_delay_sender(
        std::chrono::duration<Rep, Period> rel)
        : state_{
              .ts = to_timespec_(rel),
              .timespec_is_absolute = false,
              .timespec_is_utc_clock = false}
    {
    }

    //! Complete when this future point in time passes (monotonic clock
    //! invariant to system sleep)
    explicit constexpr timed_delay_sender(
        std::chrono::steady_clock::time_point dle)
        : state_{
              .ts = to_timespec_(dle),
              .timespec_is_absolute = true,
              .timespec_is_utc_clock = false}
    {
    }

    //! Complete when this future point in time passes (UTC date time clock)
    explicit constexpr timed_delay_sender(
        std::chrono::system_clock::time_point dle)
        : state_{
              .ts = to_timespec_(dle),
              .timespec_is_absolute = true,
              .timespec_is_utc_clock = true}
    {
    }

    template <class Rep, class Period>
    void reset(std::chrono::duration<Rep, Period> rel)
    {
        state_.ts = to_timespec_(rel);
    }

    void reset(std::chrono::steady_clock::time_point dle)
    {
        state_.ts = to_timespec_(dle);
    }

    void reset(std::chrono::system_clock::time_point dle)
    {
        state_.ts = to_timespec_(dle);
    }

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        io_state->executor()->submit_timed_invocation_request(
            &state_, io_state);
        return success();
    }

    result_type
    completed(erased_connected_operation *, result<void> res) noexcept
    {
        // Ignore ETIME failures, which simply mean the timer fired
        if (!res &&
            res.assume_error() ==
                errc::stream_timeout /* This is a stupid name for ETIME */) {
            return success();
        }
        return res;
    }
};

static_assert(sizeof(timed_delay_sender) == 24);
static_assert(alignof(timed_delay_sender) == 8);
static_assert(sender<timed_delay_sender>);

/*! \class threadsafe_sender
\brief A Sender which completes on the kernel thread executing an `AsyncIO`
instance, but which can be initiated thread safely from any other kernel
thread.

```
Benchmarking threadsafe_sender ...
   Did 1.5978e+06 completions per second
```
*/
class threadsafe_sender
{
public:
    using result_type = result<void>;

    static constexpr operation_type my_operation_type =
        operation_type::threadsafeop;
    static constexpr bool own_write_buffer = false;

public:
    threadsafe_sender() = default;

    void reset() {}

    result<void> operator()(erased_connected_operation *io_state) noexcept
    {
        io_state->executor()->submit_threadsafe_invocation_request(io_state);
        return success();
    }
};

static_assert(sizeof(threadsafe_sender) == 1);
static_assert(alignof(threadsafe_sender) == 1);
static_assert(sender<threadsafe_sender>);

MONAD_ASYNC_NAMESPACE_END
