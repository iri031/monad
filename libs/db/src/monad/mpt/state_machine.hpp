#pragma once

#include <monad/mpt/config.hpp>

#include <memory>
#include <stddef.h>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;

struct StateMachine
{
protected:
    size_t depth{0};
    bool compact_enabled{true};

public:
    virtual ~StateMachine() = default;
    virtual std::unique_ptr<StateMachine> clone() const = 0;
    virtual void down(unsigned char nibble) = 0;
    virtual void up(size_t) = 0;
    virtual Compute &get_compute() const = 0;
    virtual bool cache() const = 0;
    virtual bool compact() const = 0;

    virtual bool auto_expire() const
    {
        return false;
    }

    void reset()
    {
        depth = 0;
    }

    void toggle_compact(bool enable)
    {
        compact_enabled = enable;
    }

    bool need_compact() const
    {
        return compact_enabled && compact() && !auto_expire();
    }

    size_t get_depth() const noexcept
    {
        return depth;
    }
};

MONAD_MPT_NAMESPACE_END
