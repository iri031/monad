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
        auto c = code_analysis->post_increment_execution_count();
        if ((c+1) % 1000 == 0) {
            std::cout << "compile job queue size = " << jit.job_count() << " this exec count = " << c << " goal = " << 9999 << std::endl;
        }
        if (c == 9999) {
            jit.add_compile_job(msg.code_address, code_analysis);
        }
        //jit.debug_wait_for(msg.code_address);
        return baseline_execute_evmone_nonempty(msg, rev, host, *code_analysis);
    }

    evmc_result result = jit.execute(msg, rev, host, *code_analysis);

    //std::cout << "execution gas used: " << (msg.gas - result.gas_left) << std::endl;
    //std::cout << "execution gas left: " << result.gas_left << std::endl;

    return evmc::Result{result};
}
#endif // MONAD_JIT

//static tbb::concurrent_queue<std::chrono::duration<int64_t, std::nano>> times;
//static std::atomic<size_t> count;

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

    std::cout << "bytecode\n";
    for (unsigned b : code_analysis->executable_code) {
        std::cout << std::format("{:02x}", b);
    }
    std::cout << std::endl;
    */

#ifdef MONAD_JIT
    auto result = baseline_execute_monad_jit(msg, rev, host, code_analysis, jit);
#else
    (void)jit;
    auto result = baseline_execute_evmone(msg, rev, host, *code_analysis);
#endif

    /*
    auto end_time = std::chrono::high_resolution_clock::now();

    times.push(end_time - start_time);
    size_t n = count.fetch_add(1) + 1;
    static constexpr size_t N = 500000;
    if (n % N == 0) {
        int64_t total = 0;
        for (size_t i = 0; i < N; ++i) {
            std::chrono::duration<int64_t, std::nano> t;
            bool b = times.try_pop(t);
            MONAD_ASSERT(b);
            total += t.count();
        }
        int64_t avg = total / N;
        std::cout << "avg runtime of " << n << " messages was: " << avg << " ns" << std::endl;
    }

    std::cout << "END baseline_execute address ";
    for (auto b : msg.code_address.bytes)
        printf("%02X", (int)b);
    std::cout << '\n' << "TIME: " << (end_time - start_time) << std::endl;

    for (auto b : msg.code_address.bytes) {
        std::cout << std::format("{:02x}", b);
    }
    std::cout << " => " << "gas_left=" << result.gas_left << ", gas_refund=" << result.gas_refund << ", status_code=";
    switch (result.status_code) {
    case EVMC_SUCCESS:
        std::cout << "EVMC_SUCCESS" << std::endl;;
        break;
    case EVMC_FAILURE:
        std::cout << "EVMC_FAILURE" << std::endl;
        break;
    case EVMC_REVERT:
        std::cout << "EVMC_REVERT" << std::endl;
        break;
    case EVMC_OUT_OF_GAS:
        std::cout << "EVMC_OUT_OF_GAS" << std::endl;
        break;
    case EVMC_INVALID_INSTRUCTION:
        std::cout << "EVMC_INVALID_INSTRUCTION" << std::endl;
        break;
    case EVMC_UNDEFINED_INSTRUCTION:
        std::cout << "EVMC_UNDEFINED_INSTRUCTION" << std::endl;
        break;
    case EVMC_STACK_OVERFLOW:
        std::cout << "EVMC_STACK_OVERFLOW" << std::endl;
        break;
    case EVMC_STACK_UNDERFLOW:
        std::cout << "EVMC_STACK_UNDERFLOW" << std::endl;
        break;
    case EVMC_BAD_JUMP_DESTINATION:
        std::cout << "EVMC_BAD_JUMP_DESTINATION" << std::endl;
        break;
    case EVMC_INVALID_MEMORY_ACCESS:
        std::cout << "EVMC_INVALID_MEMORY_ACCESS" << std::endl;
        break;
    case EVMC_CALL_DEPTH_EXCEEDED:
        std::cout << "EVMC_CALL_DEPTH_EXCEEDED" << std::endl;
        break;
    case EVMC_STATIC_MODE_VIOLATION:
        std::cout << "EVMC_STATIC_MODE_VIOLATION" << std::endl;
        break;
    case EVMC_PRECOMPILE_FAILURE:
        std::cout << "EVMC_PRECOMPILE_FAILURE" << std::endl;
        break;
    case EVMC_CONTRACT_VALIDATION_FAILURE:
        std::cout << "EVMC_CONTRACT_VALIDATION_FAILURE" << std::endl;
        break;
    case EVMC_ARGUMENT_OUT_OF_RANGE:
        std::cout << "EVMC_ARGUMENT_OUT_OF_RANGE" << std::endl;
        break;
    case EVMC_WASM_UNREACHABLE_INSTRUCTION:
        std::cout << "EVMC_WASM_UNREACHABLE_INSTRUCTION" << std::endl;
        break;
    case EVMC_WASM_TRAP:
        std::cout << "EVMC_WASM_TRAP" << std::endl;
        break;
    case EVMC_INSUFFICIENT_BALANCE:
        std::cout << "EVMC_INSUFFICIENT_BALANCE" << std::endl;
        break;
    case EVMC_INTERNAL_ERROR:
        std::cout << "EVMC_INTERNAL_ERROR" << std::endl;
        break;
    case EVMC_REJECTED:
        std::cout << "EVMC_REJECTED" << std::endl;
        break;
    case EVMC_OUT_OF_MEMORY:
        std::cout << "EVMC_OUT_OF_MEMORY" << std::endl;
        break;
    };
    */

    return result;
}

MONAD_NAMESPACE_END
