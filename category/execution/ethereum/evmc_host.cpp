#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

EvmcHostBase::EvmcHostBase(
    CallTracerBase &call_tracer, evmc_tx_context const &tx_context,
    BlockHashBuffer const &block_hash_buffer, State &state,
    std::function<evmc::Result(EvmcHostBase &, evmc_message const &)> call,
    std::function<evmc::Result(EvmcHostBase &, evmc_message const &)>
        create) noexcept
    : tx_context_{tx_context}
    , block_hash_buffer_{block_hash_buffer}
    , state_{state}
    , call_tracer_{call_tracer}
    , call_{call}
    , create_{create}
{
}

bytes32_t EvmcHostBase::get_storage(
    Address const &address, bytes32_t const &key) const noexcept
{
    return state_.get_storage(address, key);
}

evmc_storage_status EvmcHostBase::set_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    return state_.set_storage(address, key, value);
}

evmc::uint256be EvmcHostBase::get_balance(Address const &address) const noexcept
{
    return state_.get_balance(address);
}

size_t EvmcHostBase::get_code_size(Address const &address) const noexcept
{
    return state_.get_code_size(address);
}

bytes32_t EvmcHostBase::get_code_hash(Address const &address) const noexcept
{
    if (state_.account_is_dead(address)) {
        return bytes32_t{};
    }
    return state_.get_code_hash(address);
}

size_t EvmcHostBase::copy_code(
    Address const &address, size_t offset, uint8_t *data,
    size_t size) const noexcept
{
    return state_.copy_code(address, offset, data, size);
}

evmc_tx_context EvmcHostBase::get_tx_context() const noexcept
{
    return tx_context_;
}

bytes32_t
EvmcHostBase::get_block_hash(int64_t const block_number) const noexcept
{
    MONAD_ASSERT(block_number >= 0);
    return block_hash_buffer_.get(static_cast<uint64_t>(block_number));
};

void EvmcHostBase::emit_log(
    Address const &address, uint8_t const *data, size_t data_size,
    bytes32_t const topics[], size_t num_topics) noexcept
{
    Receipt::Log log{.data = {data, data_size}, .address = address};
    for (auto i = 0u; i < num_topics; ++i) {
        log.topics.push_back({topics[i]});
    }
    state_.store_log(std::move(log));
}

evmc_access_status EvmcHostBase::access_storage(
    Address const &address, bytes32_t const &key) noexcept
{
    return state_.access_storage(address, key);
}

bytes32_t EvmcHostBase::get_transient_storage(
    Address const &address, bytes32_t const &key) const noexcept
{
    return state_.get_transient_storage(address, key);
}

void EvmcHostBase::set_transient_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    return state_.set_transient_storage(address, key, value);
}

MONAD_NAMESPACE_END
