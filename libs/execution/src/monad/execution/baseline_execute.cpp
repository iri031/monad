#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/execution/baseline_execute.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/monad_jit_compiler.hpp>

#include <evmone/baseline.hpp>
#include <evmone/baseline_instruction_table.hpp>

#ifndef __clang__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored_attributes "clang::"
#endif
#include <evmone/execution_state.hpp>
#ifndef __clang__
    #pragma GCC diagnostic pop
#endif

#include <evmone/vm.hpp>

#ifdef EVMONE_TRACING
    #include <evmone/tracing.hpp>

    #include <quill/Quill.h>

    #include <sstream>
#endif

#include <chrono>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <iostream>

MONAD_NAMESPACE_BEGIN

static evmc::Result baseline_execute_evmone_nonempty(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    ::evmone::baseline::CodeAnalysis const &code_analysis)
{
    auto const execution_state = std::make_unique<evmone::ExecutionState>(
        msg,
        rev,
        host->get_interface(),
        host->to_context(),
        code_analysis.executable_code,
        byte_string_view{});

    execution_state->analysis.baseline = &code_analysis;

    auto const &cost_table = evmone::baseline::get_baseline_cost_table(
        execution_state->rev, code_analysis.eof_header.version);

    evmone::VM vm{};

    #ifdef EVMONE_TRACING
        std::ostringstream trace_ostream;
        vm.add_tracer(evmone::create_instruction_tracer(trace_ostream));
    #endif

    auto const gas = evmone::baseline::monad_execute(
        vm.get_tracer(), msg.gas, *execution_state, cost_table, code_analysis);

    auto const gas_left = (execution_state->status == EVMC_SUCCESS ||
                           execution_state->status == EVMC_REVERT)
                              ? gas
                              : 0;
    auto const gas_refund = (execution_state->status == EVMC_SUCCESS)
                                ? execution_state->gas_refund
                                : 0;

    MONAD_ASSERT(
        execution_state->output_size != 0 ||
        execution_state->output_offset == 0);
    auto const result = evmc::make_result(
        execution_state->status,
        gas_left,
        gas_refund,
        execution_state->output_size != 0
            ? &execution_state->memory[execution_state->output_offset]
            : nullptr,
        execution_state->output_size);

    //std::cout << "execution gas used: " << (msg.gas - gas_left) << std::endl;
    //std::cout << "execution gas left: " << gas_left << std::endl;

    if (MONAD_UNLIKELY(vm.get_tracer() != nullptr)) {
        vm.get_tracer()->notify_execution_end(result);
    }

    #ifdef EVMONE_TRACING
        LOG_TRACE_L1("{}", trace_ostream.str());
    #endif

    return evmc::Result{result};
}

evmc::Result baseline_execute_evmone(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    ::evmone::baseline::CodeAnalysis const &code_analysis)
{
    if (code_analysis.executable_code.empty()) {
        return evmc::Result{EVMC_SUCCESS, msg.gas};
    }
    return baseline_execute_evmone_nonempty(msg, rev, host, code_analysis);
}

#ifdef MONAD_JIT
evmc::Result baseline_execute_monad_jit(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    std::shared_ptr<CodeAnalysis> code_analysis, MonadJitCompiler &jit)
{
    if (code_analysis->executable_code.empty()) {
        return evmc::Result{EVMC_SUCCESS, msg.gas};
    }

    if (code_analysis->native_contract_main() == nullptr) {
        jit.add_compile_job(msg.code_address, code_analysis);
        //jit.debug_wait_for(msg.code_address);
        return baseline_execute_evmone_nonempty(msg, rev, host, *code_analysis);
    }

    evmc_result result = jit.execute(msg, rev, host, *code_analysis);

    //std::cout << "execution gas used: " << (msg.gas - result.gas_left) << std::endl;
    //std::cout << "execution gas left: " << result.gas_left << std::endl;

    return evmc::Result{result};
}
#endif // MONAD_JIT

evmc::Result baseline_execute(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    std::shared_ptr<CodeAnalysis> code_analysis, MonadJitCompiler &jit)
{
    /*
    std::cout << "START baseline_execute address ";
    for (auto b : msg.code_address.bytes)
        printf("%02X", (int)b);
    std::cout << std::endl;

    auto start_time = std::chrono::high_resolution_clock::now();
    */

#ifdef MONAD_JIT
    auto result = baseline_execute_monad_jit(msg, rev, host, code_analysis, jit);
#else
    (void)jit;
    auto result = baseline_execute_evmone(msg, rev, host, *code_analysis);
#endif

    /*
    auto end_time = std::chrono::high_resolution_clock::now();

    std::cout << "END baseline_execute address ";
    for (auto b : msg.code_address.bytes)
        printf("%02X", (int)b);
    std::cout << '\n' << "TIME: " << (end_time - start_time) << std::endl;
    */

    return result;
}

MONAD_NAMESPACE_END
