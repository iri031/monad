#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/execution/monad_precompiles.hpp>
#include <monad/state3/state.hpp>

#include <functional>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using GasCostFn = std::function<uint64_t(monad_revision, byte_string_view)>;
using ExecuteFn =
    std::function<PrecompileResult(Address const &, byte_string_view, State &)>;

constexpr Address MONAD_PRECOMPILE_BASE =
    0xff00000000000000000000000000000000000000_address;

constexpr unsigned num_monad_precompiles(monad_revision const rev)
{
    switch (rev) {
    case MONAD_ZERO:
    case MONAD_ONE:
    case MONAD_TWO:
        return 0;
    case MONAD_THREE:
        return 1;
    default:
        MONAD_ASSERT(false);
    }
}

std::array<
    std::pair<GasCostFn, ExecuteFn>,
    num_monad_precompiles(MONAD_THREE) + 1> const MONAD_PRECOMPILES_DISPATCH{{
    {nullptr, nullptr}, // precompiles start at address 0xff..01
    {max_reserve_balance_cost, max_reserve_balance_execute},
}};

Address max_monad_precompile_address(monad_revision const rev)
{
    Address address{num_monad_precompiles(rev)};
    address.bytes[0] = 0xff;
    return address;
}

bool is_monad_precompile(monad_revision const rev, Address const &address)
{
    return address > MONAD_PRECOMPILE_BASE &&
           address <= max_monad_precompile_address(rev);
}

bool is_zero_depth_only(Address const &address)
{
    return address == MAX_RESERVE_BALANCE_ADDRESS;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

uint64_t max_reserve_balance_cost(monad_revision, byte_string_view)
{
    return 22100;
}

PrecompileResult max_reserve_balance_execute(
    Address const &sender, byte_string_view const data, State &state)
{
    if (MONAD_UNLIKELY(!state.account_exists(MAX_RESERVE_BALANCE_ADDRESS))) {
        state.set_nonce(MAX_RESERVE_BALANCE_ADDRESS, 1);
    }

    if (data.empty()) {
        return PrecompileResult::failure();
    }

    bytes32_t ret{};
    if (data[0] == 0x01) { // set max reserve balance
        byte_string_view encoded = data.substr(1);
        auto const result = rlp::decode_unsigned<uint256_t>(encoded);
        if (result.has_error() || !encoded.empty()) {
            return PrecompileResult::failure();
        }
        bytes32_t const key = to_bytes(to_byte_string_view(sender.bytes));
        ret = state.get_storage(MAX_RESERVE_BALANCE_ADDRESS, key);
        bytes32_t const val = data[1] >= 0x80 ? to_bytes(data.substr(2))
                                              : to_bytes(data.substr(1));
        state.set_storage(MAX_RESERVE_BALANCE_ADDRESS, key, val);
    }
    else if (data[0] == 0x02) { // get max reserve balance
        byte_string_view const address = data.substr(1);
        if (address.size() != sizeof(Address)) {
            return PrecompileResult::failure();
        }
        ret = state.get_storage(MAX_RESERVE_BALANCE_ADDRESS, to_bytes(address));
    }
    else {
        return PrecompileResult::failure();
    }
    byte_string const enc =
        rlp::encode_string2(rlp::zeroless_view(to_byte_string_view(ret.bytes)));
    uint8_t *const obuf = static_cast<uint8_t *>(std::malloc(enc.size()));
    MONAD_ASSERT(obuf != nullptr);
    std::memcpy(obuf, enc.data(), enc.size());
    return PrecompileResult{
        .status_code = EVMC_SUCCESS, .obuf = obuf, .output_size = enc.size()};
}

std::optional<evmc::Result> check_call_monad_precompile(
    monad_revision const rev, evmc_message const &msg, State &state)
{
    auto const &address = msg.code_address;

    if (!is_monad_precompile(rev, address)) {
        return std::nullopt;
    }
    if (is_zero_depth_only(address) && msg.depth != 0) {
        return std::nullopt;
    }

    auto const i = address.bytes[sizeof(address.bytes) - 1];
    auto const [gas_cost_fn, execute_fn] = MONAD_PRECOMPILES_DISPATCH.at(i);
    byte_string_view const input{msg.input_data, msg.input_size};
    uint64_t const cost = gas_cost_fn(rev, input);
    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    auto const [status_code, output_buffer, output_size] =
        execute_fn(msg.sender, input, state);
    return evmc::Result{evmc_result{
        .status_code = status_code,
        .gas_left = (status_code == EVMC_SUCCESS)
                        ? msg.gas - static_cast<int64_t>(cost)
                        : 0,
        .gas_refund = 0,
        .output_data = output_buffer,
        .output_size = output_size,
        .release = evmc_free_result_memory,
        .create_address = {},
        .padding = {},
    }};
}

MONAD_NAMESPACE_END
