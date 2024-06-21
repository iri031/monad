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

template<typename T>
struct task_delete
{
    void operator()(monad_fiber_task_t * task)
    {
        (*task->destroy)(task);
    }
};

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

private:
    monad_fiber_channel_t impl_;
};


// write a shared state
namespace detail
{

}

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
        T val{};

        auto p = impl_.lock();
        if (!p)
            MONAD_FIBER_THROW_SYSTEM_EC(EPIPE, "promise expired");


        auto code = p->read(val);
        if (code)
            MONAD_FIBER_THROW_SYSTEM_EC(code, "read");
        else
            p->close();
        
        return val;
    }

  private:
    template<typename>
    friend struct promise;

    std::weak_ptr<channel<T>> impl_;
};


template<>
inline void future<void>::get()
{
    auto p = impl_.lock();
    if (!p)
        MONAD_FIBER_THROW_SYSTEM_EC(EPIPE, "promise expired");

    auto code = p->read();
    if (code)
        MONAD_FIBER_THROW_SYSTEM_EC(code, "read");
    else
        p->close();


}

template< typename R >
struct promise
{
    promise() : impl_(std::make_shared<channel<R>>(1u)) {}

    template< typename Allocator >
    promise( std::allocator_arg_t, Allocator alloc)
            : impl_(std::allocate_shared<channel<R>>(std::move(alloc), 1u))
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

    template<typename T,
              typename = std::enable_if_t<
                  std::is_same_v<T, R> || !std::is_void_v<R>>>
    void set_value(T && value)
    {
        auto code = impl_->send(std::forward<T>(value));
        if (code)
            MONAD_FIBER_THROW_SYSTEM_EC(code, "channel::send");
    }

  private:

    std::shared_ptr<channel<R>> impl_;
};

MONAD_FIBER_NAMESPACE_END
