#pragma once

#include <monad/fiber/channel.h>
#include <monad/fiber/scheduler.h>

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

MONAD_FIBER_NAMESPACE_END
