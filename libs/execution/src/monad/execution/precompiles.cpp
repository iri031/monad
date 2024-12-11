#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/execution/bn_wrapper.h>

#include <silkpre/precompile.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/helpers.h>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

consteval unsigned num_precompiles(evmc_revision const rev)
{
    switch (rev) {
    case EVMC_FRONTIER:
    case EVMC_HOMESTEAD:
    case EVMC_TANGERINE_WHISTLE:
    case EVMC_SPURIOUS_DRAGON:
        return 4;
    case EVMC_BYZANTIUM:
    case EVMC_CONSTANTINOPLE:
    case EVMC_PETERSBURG:
        return 8;
    case EVMC_ISTANBUL:
    case EVMC_BERLIN:
    case EVMC_LONDON:
    case EVMC_PARIS:
    case EVMC_SHANGHAI:
    case EVMC_CANCUN: // TODO(kkuehler): change to 10 after
                      // https://github.com/monad-crypto/monad/pull/887
        return 9;
    default:
        MONAD_ASSERT(false);
    }
}

template <evmc_revision rev>
bool is_precompile(Address const &address) noexcept
{
    static constexpr auto max_address = Address{num_precompiles(rev)};

    if (MONAD_LIKELY(address > max_address)) {
        return false;
    }

    if (MONAD_UNLIKELY(evmc::is_zero(address))) {
        return false;
    }

    return true;
}

EXPLICIT_EVMC_REVISION(is_precompile);

static void right_pad(std::basic_string<uint8_t>& str, const size_t min_size) noexcept {
    if (str.length() < min_size) {
        str.resize(min_size, '\0');
    }
}

static SilkpreOutput bn_wrapper_bn_add_run(const uint8_t* ptr, size_t len) {
    std::basic_string<uint8_t> input(ptr, len);
    right_pad(input, 128);

    uint8_t* out{static_cast<uint8_t*>(std::malloc(64))};
    auto retval = bn_add_run(input.data(), out);
    if(retval != 0)
    {
    std::free(out);
    return {nullptr, 0};
    }
    return {out, 64 };

}

static SilkpreOutput bn_wrapper_bn_mul_run(const uint8_t* ptr, size_t len) {
    std::basic_string<uint8_t> input(ptr, len);
    right_pad(input, 96);

    uint8_t* out{static_cast<uint8_t*>(std::malloc(64))};

    auto retval = bn_mul_run(input.data(), out);
    if (retval != 0)
    {
    std::free(out);
    return {nullptr, 0};
    }
    return {out, 64};
}

static constexpr size_t kSnarkvStride{192};

static SilkpreOutput bn_wrapper_bn_snarkv_run(const uint8_t* ptr, size_t len) {
    if (len % kSnarkvStride != 0) {
        return {nullptr, 0};
    }
    uint32_t retval = bn_snarkv_run(ptr, len);
    if (retval != 0 && retval != 1)
    {
             return {nullptr, 0};
    }
    uint8_t* out{static_cast<uint8_t*>(std::malloc(32))};
    std::memset(out, 0, 32);
    out[31] = (uint8_t)retval;
    return {out, 32};
}

const SilkpreContract precompileContracts[SILKPRE_NUMBER_OF_ISTANBUL_CONTRACTS] = {
    {silkpre_ecrec_gas, silkpre_ecrec_run},       {silkpre_sha256_gas, silkpre_sha256_run},
    {silkpre_rip160_gas, silkpre_rip160_run},     {silkpre_id_gas, silkpre_id_run},
    {silkpre_expmod_gas, silkpre_expmod_run},     {silkpre_bn_add_gas, bn_wrapper_bn_add_run},
    {silkpre_bn_mul_gas, bn_wrapper_bn_mul_run},     {silkpre_snarkv_gas, bn_wrapper_bn_snarkv_run},
    {silkpre_blake2_f_gas, silkpre_blake2_f_run},
};

template <evmc_revision rev>
std::optional<evmc::Result> check_call_precompile(evmc_message const &msg)
{
    auto const &address = msg.code_address;

    if (!is_precompile<rev>(address)) {
        return std::nullopt;
    }

    auto const i = address.bytes[sizeof(address.bytes) - 1];

    auto const gas_func = precompileContracts[i - 1].gas;

    auto const cost = gas_func(msg.input_data, msg.input_size, rev);

    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    auto const run_func = precompileContracts[i - 1].run;

    auto const output = run_func(
        (msg.input_data != nullptr || msg.input_size != 0)
            ? msg.input_data
            : (uint8_t const *)"",
        msg.input_size);

    if (MONAD_UNLIKELY(!output.data)) {
        return evmc::Result{evmc_status_code::EVMC_PRECOMPILE_FAILURE};
    }

    return evmc::Result{evmc_result{
        .status_code = evmc_status_code::EVMC_SUCCESS,
        .gas_left = msg.gas - static_cast<int64_t>(cost),
        .gas_refund = 0,
        .output_data = output.data,
        .output_size = output.size,
        .release = evmc_free_result_memory,
        .create_address = {},
        .padding = {},
    }};
}

EXPLICIT_EVMC_REVISION(check_call_precompile);

MONAD_NAMESPACE_END
