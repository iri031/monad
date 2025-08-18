#pragma once

#include <category/mpt2/config.hpp>

#include <boost/lockfree/spsc_queue.hpp>

#include <condition_variable>
#include <mutex>

MONAD_MPT2_NAMESPACE_BEGIN

template <typename T>
class BlockingSPSC : public boost::lockfree::spsc_queue<T>
{
    using Base = boost::lockfree::spsc_queue<T>;

public:
    BlockingSPSC(size_t capacity)
        : Base(capacity)
    {
    }

    // Blocking push: waits if the queue is full
    void push_blocking(T const &item)
    {
        std::unique_lock<std::mutex> lk(mtx_);
        while (!Base::push(item)) {
            cv_space_available_.wait(lk);
        }
    }

    void push_blocking(T &&item)
    {
        std::unique_lock<std::mutex> lk(mtx_);
        while (!Base::push(std::move(item))) {
            cv_space_available_.wait(lk);
        }
    }

    // returns true if item was consumed
    template <typename Func>
    bool consume_one_notify_drained(Func &&f)
    {
        bool consumed = false;
        Base::consume_one([&](T const &item) {
            f(item); // process while holding access to front element
            consumed = true;
        });
        if (consumed) {
            cv_space_available_.notify_one(); // space available for producer
            if (this->read_available() == 0) {
                cv_drained_.notify_all(); // queue completely drained
            }
        }
        return consumed;
    }

    // Producer can wait until the consumer drains the queue
    void wait_until_drained()
    {
        std::unique_lock<std::mutex> lk(mtx_);
        cv_drained_.wait(lk, [&] { return this->read_available() == 0; });
    }

    bool empty() const
    {
        return this->read_available() == 0;
    }

private:
    std::mutex mtx_;
    std::condition_variable cv_space_available_;
    std::condition_variable cv_drained_;
};

MONAD_MPT2_NAMESPACE_END
