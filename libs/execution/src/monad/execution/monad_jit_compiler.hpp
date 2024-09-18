#pragma once

#include <monad/execution/code_analysis.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <tbb/concurrent_hash_map.h>
#include <tbb/concurrent_queue.h>

#include <condition_variable>
#include <mutex>
#include <thread>

#include <iostream>
#include <format>

#define MONAD_JIT

MONAD_NAMESPACE_BEGIN

class MonadJitCompiler
{
#ifdef MONAD_JIT
    using MonadJitExecuteFn = evmc_result (*)(
        evmc_vm *vm,
        evmc_host_interface const *host,
        evmc_host_context *context,
        evmc_revision rev,
        evmc_message const *msg,
        uint8_t const *code,
        size_t code_size,
        void *contract_main
    );

    using MonadJitCompileFn = bool (*)(
            bytes32_t const *, uint8_t const* code, size_t code_size);

    struct EvmcAddressHashCompare
    {
        size_t hash(bytes32_t const &x) const;
        bool equal(bytes32_t const& x, bytes32_t const& y) const;
    };

    using CompileJobMap =
        tbb::concurrent_hash_map<
            bytes32_t,
            std::shared_ptr<CodeAnalysis>,
            EvmcAddressHashCompare>;

    using CompileJobAccessor = CompileJobMap::accessor;

    using CompileJobQueue = tbb::concurrent_queue<bytes32_t>;

    char const *jit_directory_;

    evmc::VM vm_;

    void *vmhandle_;
    void *libhandle_;

    MonadJitExecuteFn monad_jit_execute_;
    MonadJitCompileFn monad_jit_compile_;

    CompileJobMap compile_job_map_;
    CompileJobQueue compile_job_queue_;
    std::condition_variable compile_job_cv_;
    std::mutex compile_job_mutex_;
    std::unique_lock<std::mutex> compile_job_lock_;

    std::thread compiler_thread_;
    std::atomic<bool> stop_flag_;

public:
    MonadJitCompiler();

    ~MonadJitCompiler();

    void restart_compiler(bool remove_contracts);

    size_t job_count() const {
        return compile_job_map_.size();
    }

    void add_compile_job(
        bytes32_t const &a,
        std::shared_ptr<CodeAnalysis> const &code_analysis)
    {
        if (!compile_job_map_.insert({a, code_analysis}))
            return;
        compile_job_queue_.push(a);
        compile_job_cv_.notify_one();
    }

    evmc_result execute(
        evmc_message const &msg,
        evmc_revision const rev,
        evmc::Host *const host,
        CodeAnalysis const &code_analysis)
    {
        return monad_jit_execute_(
            vm_.get_raw_pointer(),
            &host->get_interface(),
            host->to_context(),
            rev,
            &msg,
            code_analysis.executable_code.data(),
            code_analysis.executable_code.size(),
            code_analysis.native_contract_main());
    }

    void enable_remove_compiled_contracts();

    void debug_wait_for(bytes32_t const& a);

private:
    void run_compile_loop();
    void dispense_compile_jobs();
    void compile(bytes32_t const &, CodeAnalysis &);
    void remove_compiled_contracts();
    void stop_compiler();
    void start_compiler();
#endif // MONAD_JIT
};

MONAD_NAMESPACE_END
