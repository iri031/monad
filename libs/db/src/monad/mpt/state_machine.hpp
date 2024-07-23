#pragma once

#include <monad/mpt/config.hpp>

#include <memory>
#include <stddef.h>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;
enum class CacheOption : uint8_t;

struct StateMachine
{
    enum class TrieType : uint8_t
    {
        Prefix,
        State,
        Code,
        Receipt
    };

    TrieType trie_section{TrieType::Prefix};
    virtual ~StateMachine() = default;
    virtual std::unique_ptr<StateMachine> clone() const = 0;
    virtual void down(unsigned char nibble) = 0;
    virtual void up(size_t) = 0;
    virtual Compute &get_compute() const = 0;
    virtual bool cache() const = 0;
    virtual bool compact() const = 0;
};

MONAD_MPT_NAMESPACE_END
