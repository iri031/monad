#pragma once

#include <monad/mpt/config.hpp>

#include <memory>
#include <stddef.h>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;

struct StateMachine
{
private:
    bool compact_enabled{true};

public:
    virtual ~StateMachine() = default;
    virtual std::unique_ptr<StateMachine> clone() const = 0;
    virtual void down(unsigned char nibble) = 0;
    virtual void up(size_t) = 0;
    virtual Compute &get_compute() const = 0;
    virtual bool cache() const = 0;
    virtual bool compactable() const = 0;

    virtual bool auto_expire() const
    {
        return false;
    }

    void set_compact(bool const compact)
    {
        compact_enabled = compact;
    }

    bool compact() const
    {
        return compact_enabled && compactable();
    }
};

MONAD_MPT_NAMESPACE_END
