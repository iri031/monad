#pragma once

#include <monad/config.hpp>

#include <monad/core/byte_string.hpp>

#include <atomic>

#include <evmone/baseline.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

class CodeAnalysis : public ::evmone::baseline::CodeAnalysis {
    // Handle returned by dlopen:
    std::atomic<void *> native_contract_code_;
    // Native code for the smart contract main function:
    std::atomic<void *> native_contract_main_;
    // Whether native contract has been successfully loaded:
    std::atomic_flag is_native_contract_code_loaded_;
    // Number of times this contract has been executed:
    std::atomic<size_t> execution_count_;
public:
    CodeAnalysis(CodeAnalysis &&);
    CodeAnalysis(::evmone::baseline::CodeAnalysis &&);
    ~CodeAnalysis();
    bool is_native_contract_code_loaded() const
    {
        return is_native_contract_code_loaded_.test(std::memory_order_acquire);
    }
    void load_native_contract_code(char const *jit_dir, evmc_address const &);
    void *native_contract_main() const
    {
        return native_contract_main_.load(std::memory_order_acquire);
    }
    size_t post_increment_execution_count()
    {
        return execution_count_.fetch_add(1, std::memory_order_acq_rel);
    }
};

/// FIXME - no need to perform evmone analysis if we can load the native contract code.
inline CodeAnalysis analyze(byte_string_view const &code)
{
    return {evmone::baseline::analyze(EVMC_FRONTIER, code)}; // TODO rev
}

MONAD_NAMESPACE_END
