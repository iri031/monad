#pragma once

#include <category/core/assert.h>
#include <category/mpt2/config.hpp>
#include <category/mpt2/util.hpp>

#include <boost/lockfree/spsc_queue.hpp>

#include <atomic>
#include <cstdint>
#include <thread>

MONAD_MPT2_NAMESPACE_BEGIN

class UpdateAux;

class AsyncWorker
{
public:
    AsyncWorker(UpdateAux &aux);

    ~AsyncWorker()
    {
        drain_and_stop();
    }

    void drain_and_stop();

private:
    UpdateAux &aux_;
    std::atomic<bool> running_;
    std::thread worker_thread_;

    void run();
};

MONAD_MPT2_NAMESPACE_END
