#pragma once

#include <monad/fiber/channel.h>
#include <monad/fiber/config.hpp>
#include <monad/fiber/scheduler.h>

#include <boost/system/result.hpp>


#define MONAD_FIBER_THROW_SYSTEM_EC(Code, Message)                           \
    do {                                                                     \
        boost::system::error_code _ec_;                                      \
        constexpr static boost::source_location loc{BOOST_CURRENT_LOCATION}; \
        _ec_.assign((Code), boost::system::system_category(), &loc);         \
        boost::throw_exception(boost::system::system_error(_ec_, (Message)), \
                               BOOST_CURRENT_LOCATION);                      \
    } while(true)


MONAD_FIBER_NAMESPACE_BEGIN


struct scheduler : monad_fiber_scheduler_t
{
    scheduler(size_t threads)
    {
        monad_fiber_scheduler_create(this, threads, &monad_fiber_init_main);
    }
    scheduler(const scheduler &) = delete;

    ~scheduler() { monad_fiber_scheduler_destroy(this); }

    void work() { monad_fiber_scheduler_work(this); }
    void stop() { monad_fiber_scheduler_stop(this); }


    void post    (monad_fiber_task_t * task) { monad_fiber_scheduler_post(this, task); }
    void dispatch(monad_fiber_task_t * task) { monad_fiber_scheduler_dispatch(this, task); }

    bool run_one() { return monad_fiber_run_one(this); }


    monad_fiber_task_t *pop_higher_priority_task(int64_t priority)
    {
        return monad_fiber_scheduler_pop_higher_priority_task(this, priority);
    }

    static scheduler * current()
    {
        return static_cast<scheduler*>(monad_fiber_scheduler_current());
    }
};

template<typename T>
struct channel
{
    channel(size_t capacity)
    {
        monad_fiber_channel_create(&impl_, capacity, sizeof(T));
    }

    channel(const channel &) = delete;

    ~channel()
    {
        auto p = reinterpret_cast<T*>(impl_.data);
        for (auto pos = 0u; pos < impl_.size; pos++)
            p[pos].~T();

        monad_fiber_channel_destroy(&impl_);
    }


    void close() { monad_fiber_channel_close(&impl_); }

    bool try_read (      T& value) { return monad_fiber_channel_try_read(&impl_, & value);}
    bool try_write(const T& value) { return monad_fiber_channel_try_write(impl_, &value);}

    int read (      T& value) { return monad_fiber_channel_read (&impl_, &value);}
    int write(const T& value) { return monad_fiber_channel_write(&impl_, &value);}
    int send (const T& value) { return monad_fiber_channel_send (&impl_, &value);}

    size_t available() noexcept
    {
        return monad_fiber_channel_available(&impl_);
    }
private:
    monad_fiber_channel_t impl_;
};

template<typename T>
struct channel<T&>
{
    channel(size_t capacity)
    {
        monad_fiber_channel_create(&impl_, capacity, sizeof(T));
    }

    channel(const channel &) = delete;

    ~channel()
    {
        monad_fiber_channel_destroy(&impl_);
    }


    void close() { monad_fiber_channel_close(&impl_); }

    bool try_read (      T& value) { return monad_fiber_channel_try_read(&impl_, & value);}
    bool try_write(const T& value) { return monad_fiber_channel_try_write(impl_, &value);}

    int read (      T* value) { return monad_fiber_channel_read (&impl_, &value);}
    int write(      T& value) { return monad_fiber_channel_write(&impl_, &value);}
    int send (      T& value) { return monad_fiber_channel_send (&impl_, &value);}

    size_t available() noexcept
    {
        return monad_fiber_channel_available(&impl_);
    }

private:
    monad_fiber_channel_t impl_;
};


template<>
struct channel<void>
{
    channel(size_t capacity)
    {
        monad_fiber_channel_create(&impl_, capacity, 0u);
    }

    channel(const channel &) = delete;

    ~channel()
    {
        monad_fiber_channel_destroy(&impl_);
    }


    void close() { monad_fiber_channel_close(&impl_); }

    bool try_read () { return monad_fiber_channel_try_read(&impl_, nullptr);}
    bool try_write() { return monad_fiber_channel_try_write(&impl_, nullptr);}

    int read () { return monad_fiber_channel_read (&impl_, nullptr);}
    int write() { return monad_fiber_channel_write(&impl_, nullptr);}
    int send () { return monad_fiber_channel_send (&impl_, nullptr);}

    size_t available() noexcept
    {
        return monad_fiber_channel_available(&impl_);
    }

private:
    monad_fiber_channel_t impl_;
};


template< typename T >
struct future
{
    future() noexcept = default;

    future( future const& other) = delete;

    future & operator=( future const& other) = delete;

    future( future && other) noexcept = default;

    future & operator=( future && other) noexcept = default;

    ~future() = default;

    bool valid() const noexcept { return !!impl_; };

    inline T get()
    {
        std::optional<T> val{};

        if (impl_.use_count() == 1)
        {
            if (impl_->try_read(val))
                return std::move(*val);
            else
                MONAD_FIBER_THROW_SYSTEM_EC(EPIPE, "promise expired");
        }

        auto code = impl_->read(val);
        if (code)
            MONAD_FIBER_THROW_SYSTEM_EC(code, "read");
        else
            impl_->close();
        
        return *std::move(val);
    }
    bool ready() const noexcept
    {
        auto & c = *impl_;
        fprintf(stderr, "ready() %ld\n", c.available());
        return c.available() > 0u;
    }

  private:
    template<typename>
    friend struct promise;

    future( std::shared_ptr<channel<
               std::conditional_t<std::is_void_v<T>, T, std::optional<T>>
               >> impl) noexcept : impl_(std::move(impl)) {}


    std::shared_ptr<channel<
        std::conditional_t<std::is_void_v<T>, T, std::optional<T>>
        >> impl_;
};



template<>
inline void future<void>::get()
{
    MONAD_ASSERT(impl_);
    if (impl_.use_count() == 1)
    {
        if (impl_->try_read())
            return ;
        else
            MONAD_FIBER_THROW_SYSTEM_EC(EPIPE, "promise expired");
    }

    auto code = impl_->read();
    if (code)
        MONAD_FIBER_THROW_SYSTEM_EC(code, "read");
    else
        impl_->close();


}

template< typename R >
struct promise
{
    using data_type = std::conditional_t<std::is_void_v<R>, R, std::optional<R>>;
    promise() : impl_(std::make_shared<channel<data_type>>(1u)) {}

    template< typename Allocator >
    promise( std::allocator_arg_t, Allocator alloc)
            : impl_(std::allocate_shared<channel<data_type>>(std::move(alloc), 1u))
    {}

    promise( promise &&) noexcept = default;

    promise & operator=( promise &&) noexcept = default;

    promise( promise const&) = delete;

    promise & operator=( promise const&) = delete;

    ~promise() = default;


    future< R > get_future()
    {
        return future< R >{impl_};
    }

    // void call

    template<typename _ = void,
             typename = std::enable_if_t<std::is_same_v<_, R>>>
    void set_value()
    {
        auto code = impl_->send();
        if (code)
            MONAD_FIBER_THROW_SYSTEM_EC(code, "channel::send");

    }

    template<typename T = R,
              typename = std::enable_if_t<
                  std::is_same_v<T, R> || !std::is_void_v<R>>>
    void set_value(T && value)
    {
        fprintf(stderr, "%p.set_value(T) (1)\n", (void*)impl_.get());

        auto code = impl_->send(std::forward<T>(value));
        if (code)
            MONAD_FIBER_THROW_SYSTEM_EC(code, "channel::send");
        fprintf(stderr, "%p.set_value(T) (2)\n", (void*)impl_.get());
    }
    bool future_has_been_destroyed() const noexcept
    {
        return impl_.use_count() <= 1;
    }
  private:

    std::shared_ptr<channel<data_type>> impl_;
};

template<typename Func>
inline auto async(Func && func, scheduler & s) -> future<decltype(func())>
{
    using result_type = decltype(func());
    future<result_type> res;
    auto l =
        [&]() noexcept
        {
            std::decay_t<Func> f{std::forward<Func>(func)};
            promise<result_type> p;
            res = p.get_future();
            if constexpr (std::is_void_v<result_type>)
            {
                f();
                p.set_value();
            }
            else
                p.set_value(f());

        };

    monad_fiber_create(
            monad_fiber_default_stack_size, true, &s,
            [](void * p)
        {
            (*static_cast<decltype(l)*>(p))();
        },
            &l);

    return res;
}

MONAD_FIBER_NAMESPACE_END
