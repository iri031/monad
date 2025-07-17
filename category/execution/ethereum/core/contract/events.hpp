#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

MONAD_NAMESPACE_BEGIN

// Simple API for building events in a solidity compatible manner. Data should
// be encoded using the abi helpers.
class EventBuilder
{
    Receipt::Log event_;

public:
    explicit EventBuilder(Address const &account, bytes32_t const &signature)
    {
        event_.address = account;
        event_.topics.push_back(signature);
    }

    // Add an indexed parameter
    EventBuilder &add_topic(bytes32_t const &topic)
    {
        event_.topics.push_back(topic);
        return *this;
    }

    // Add a non-indexed parameter
    EventBuilder &add_data(byte_string_view const data)
    {
        event_.data += data;
        return *this;
    }

    Receipt::Log build()
    {
        return std::move(event_);
    }
};

MONAD_NAMESPACE_END
