#include "code_analysis.hpp"

#include <monad/core/assert.h>

#include <dlfcn.h>

#include <sstream>

#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

CodeAnalysis::CodeAnalysis(CodeAnalysis &&ca)
    : ::evmone::baseline::CodeAnalysis{std::move(ca)}
{
    if (ca.is_native_contract_code_loaded_.test(std::memory_order_relaxed))
        is_native_contract_code_loaded_.test_and_set(std::memory_order_relaxed);
    native_contract_code_.store(
        ca.native_contract_code_.load(std::memory_order_relaxed));
    native_contract_main_.store(
        ca.native_contract_main_.load(std::memory_order_relaxed));
}

CodeAnalysis::CodeAnalysis(::evmone::baseline::CodeAnalysis &&ca)
    : ::evmone::baseline::CodeAnalysis{std::move(ca)}
{}

CodeAnalysis::~CodeAnalysis()
{
    void *code = native_contract_code_.load(std::memory_order_acquire);
    if (code && dlclose(code))
        LOG_ERROR("dlclose failed: {}", dlerror());
}

void CodeAnalysis::load_native_contract_code(
        char const *jit_dir, evmc_address const &a)
{
    // Invariant: bytecode at address a = analysis.executable_code
    if (is_native_contract_code_loaded_.test_and_set(std::memory_order_acq_rel))
        return;

    std::ostringstream path;
    path << jit_dir;
    for (unsigned b : a.bytes) {
        path << std::format("{:02x}", b);
    }
    path << ".so";
    void *code = dlopen(path.str().c_str(), RTLD_NOW);
    // We can proceed when dlopen fails, and it is expected to fail when contract compilation has not started or finished. From my glimpse at the shared library format, it seems that dlopen will correctly fail if the contract shared library file is only partially written to disk, because size of header and size of segments are specified in the file. See page 2-2 in https://refspecs.linuxfoundation.org/elf/TIS1.1.pdf
    if (!code) {
        is_native_contract_code_loaded_.clear(std::memory_order_release);
        return;
    }
    void *code_main = dlsym(code, "monad_nevm_contract_main");
    MONAD_ASSERT(code_main != nullptr);
    native_contract_code_.store(code, std::memory_order_release);
    native_contract_main_.store(code_main, std::memory_order_release);
}

MONAD_NAMESPACE_END
