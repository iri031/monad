#include <monad/core/assert.h>
#include <monad/execution/monad_jit_compiler.hpp>

#include <boost/functional/hash.hpp>
#include <dlfcn.h>
#include <evmc/loader.h>
#include <quill/Quill.h>

#include <chrono>
#include <filesystem>

namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN
#ifdef MONAD_JIT

size_t MonadJitCompiler::EvmcAddressHashCompare::hash(evmc_address const &x) const
{
    return boost::hash_range(x.bytes, x.bytes + sizeof x.bytes);
}
bool MonadJitCompiler::EvmcAddressHashCompare::equal(
    evmc_address const& x, evmc_address const& y) const
{
    return std::memcmp(x.bytes, y.bytes, sizeof x.bytes) == 0;
}

MonadJitCompiler::MonadJitCompiler()
    : jit_directory{std::getenv("MONAD_VM_COMPILE_DIR")}
    , is_remove_compiled_contracts_enabled{}
    , compile_job_lock{compile_job_mutex}
{
    MONAD_ASSERT(fs::is_directory(jit_directory));

    vmhandle = dlopen("libmonad_nevm_vm.so", RTLD_NOW);
    MONAD_ASSERT(vmhandle != nullptr);

    monad_jit_execute =
        (MonadJitExecuteFn) dlsym(vmhandle, "monad_jit_execute");
    MONAD_ASSERT(monad_jit_execute != nullptr);

    monad_jit_compile =
        (MonadJitCompileFn) dlsym(vmhandle, "monad_jit_compile");
    MONAD_ASSERT(monad_jit_compile != nullptr);

    evmc_loader_error_code ec = EVMC_LOADER_UNSPECIFIED_ERROR;
    vm = evmc::VM{evmc_load_and_configure("libmonad_nevm_vm.so", &ec)};
    MONAD_ASSERT(ec == EVMC_LOADER_SUCCESS);

    libhandle = dlopen("libmonad_nevm_vmlib.so", RTLD_NOW);
    MONAD_ASSERT(libhandle != nullptr);

    start_compiler();
}

MonadJitCompiler::~MonadJitCompiler()
{
    stop_compiler();
    dlclose(vmhandle);
    dlclose(libhandle);
}

void MonadJitCompiler::stop_compiler()
{
    stop_flag.store(true, std::memory_order_release);
    compile_job_cv.notify_one();
    compiler_thread.join();
}

void MonadJitCompiler::start_compiler()
{
    stop_flag.store(false, std::memory_order_release);
    compiler_thread = std::thread{[this]{ this->run_compile_loop(); }};
}

void MonadJitCompiler::restart_compiler(bool remove_contracts)
{
    stop_compiler();
    if (remove_contracts)
        remove_compiled_contracts();
    start_compiler();
}

void MonadJitCompiler::debug_wait_for(evmc_address const& a)
{
    while (compile_job_map.count(a))
        std::this_thread::sleep_for(std::chrono::microseconds(100));
}

void MonadJitCompiler::enable_remove_compiled_contracts()
{
    is_remove_compiled_contracts_enabled = true;
}

void MonadJitCompiler::remove_compiled_contracts()
{
    fs::path p{jit_directory};
    fs::directory_iterator end;
    for(fs::directory_iterator it(p); it != end; ++it) {
        auto const &p = it->path();
        try {
            if (!fs::is_regular_file(it->status()))
                continue;
            if (p.extension().compare(".so") != 0)
                continue;
            fs::remove(p);
        }
        catch(const std::exception &ex) {
            LOG_ERROR("failed deleting {} contract: {}", p, ex.what());
        }
    }
}

void MonadJitCompiler::run_compile_loop()
{
    while (!stop_flag.load(std::memory_order_acquire)) {
        compile_job_cv.wait_for(
            compile_job_lock,
            std::chrono::milliseconds(50));
        dispense_compile_jobs();
    }
}

void MonadJitCompiler::dispense_compile_jobs()
{
    evmc_address a;
    while (compile_job_queue.try_pop(a)
            && !stop_flag.load(std::memory_order_acquire)) {
        bool ok;
        CompileJobAccessor ac;

        ok = compile_job_map.find(ac, a);
        MONAD_ASSERT(ok);

        compile(a, *ac->second);

        ok = compile_job_map.erase(ac);
        MONAD_ASSERT(ok);
    }
}

void MonadJitCompiler::compile(evmc_address const &a, CodeAnalysis &code_analysis)
{
    code_analysis.load_native_contract_code(jit_directory, a);

    if (code_analysis.native_contract_main() != nullptr)
        return;

    bool success = monad_jit_compile(
        &a,
        code_analysis.executable_code.data(),
        code_analysis.executable_code.size());
    if (!success)
        return;

    code_analysis.load_native_contract_code(jit_directory, a);
}

#endif // MONAD_JIT
MONAD_NAMESPACE_END
