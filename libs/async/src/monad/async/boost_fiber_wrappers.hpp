#pragma once

#include "io_senders.hpp"
#include <monad/fiber/wrappers.hpp>

MONAD_ASYNC_NAMESPACE_BEGIN

namespace boost_fibers
{
    template <class T>
    struct promise_receiver
    {
        // We need AsyncIO to not recycle the i/o state until the future gets
        // destructed, so take over lifetime management outselves
        static constexpr bool lifetime_managed_internally = false;

        ::monad::fiber::promise<T> promise;

        void set_value(erased_connected_operation *, T res)
        {
            promise.set_value(std::move(res));
        }

        void reset()
        {
            promise = {};
        }
    };

    static_assert(receiver<promise_receiver<int>>);

    template <sender Sender>
    struct io_internal_buffer_wrap
    {
        using result_type = typename Sender::result_type;
        using receiver_type = promise_receiver<result_type>;
        using connected_state_ptr_type =
            AsyncIO::connected_operation_unique_ptr_type<Sender, receiver_type>;

        class future_with_connected_state
            : public ::monad::fiber::future<result_type>
        {
            connected_state_ptr_type state_;

            explicit future_with_connected_state(connected_state_ptr_type state)
                : ::monad::fiber::future<result_type>(
                      state->receiver().promise.get_future())
                , state_(std::move(state))
            {
                state_->initiate();
            }

        public:
            template <class... SenderArgs>
                requires(std::is_constructible_v<Sender, SenderArgs...>)
            future_with_connected_state(
                AsyncIO &io, SenderArgs &&...sender_args)
                : future_with_connected_state(
                      io.make_connected<Sender, receiver_type>(
                          std::piecewise_construct,
                          std::forward_as_tuple(
                              std::forward<SenderArgs>(sender_args)...),
                          std::tuple<>()))
            {
            }
        };
    };

    template <sender Sender>
    struct io_wrap
    {
        using result_type = typename Sender::result_type;
        using receiver_type =
            promise_receiver<result_type>;
        using connected_state_type = decltype(connect(
            std::declval<AsyncIO &>(), std::declval<Sender>(),
            std::declval<receiver_type>()));

        struct future_with_connected_state_storage
        {
            connected_state_type _state;
        };

        struct future_with_connected_state
            : public future_with_connected_state_storage
            , public ::monad::fiber::future<result_type>
        {
            template <class... SenderArgs>
                requires(std::is_constructible_v<Sender, SenderArgs...>)
            future_with_connected_state(
                AsyncIO &io, SenderArgs &&...sender_args)
                : future_with_connected_state_storage{connect<
                      Sender, receiver_type>(
                      io, std::piecewise_construct,
                      std::forward_as_tuple(
                          std::forward<SenderArgs>(sender_args)...),
                      std::tuple<>())}
                , ::monad::fiber::future<result_type>(
                      this->_state.receiver().promise.get_future())
            {
                this->_state.initiate();
            }
        };
    };

    /*! \brief Returns a Boost Fiber future of a span of bytes read. Takes the
     same arguments as `read_single_buffer_sender`.
     */
    using read_single_buffer = io_internal_buffer_wrap<
        read_single_buffer_sender>::future_with_connected_state;
    /*! \brief Returns a Boost Fiber future of a span of bytes written. Takes
     the same arguments as `write_single_buffer_sender`.
     */
    using write_single_buffer = io_internal_buffer_wrap<
        write_single_buffer_sender>::future_with_connected_state;
    /*! \brief Returns a Boost Fiber future which readies after a timeout. Takes
     the same arguments as `timed_delay_sender`.
     */
    using timed_delay =
        io_wrap<timed_delay_sender>::future_with_connected_state;
    /*! \brief Returns a Boost Fiber future which readies when execution has
    been transferred to a different `AsyncIO` instance.
     */
    using resume_execution_upon =
        io_wrap<threadsafe_sender>::future_with_connected_state;
}

MONAD_ASYNC_NAMESPACE_END
