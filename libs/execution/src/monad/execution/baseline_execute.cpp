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

#if 0
static bool is_special(evmc::address const &a) {
    static evmc::address specials[14] = {
        evmc_address{.bytes = {0x72, 0xe4, 0xf9, 0xf8, 0x08, 0xc4, 0x9a, 0x2a, 0x61, 0xde, 0x9c, 0x58, 0x96, 0x29, 0x89, 0x20, 0xdc, 0x4e, 0xee, 0xa9}},
        evmc_address{.bytes = {0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2}},
        evmc_address{.bytes = {0xa2, 0x32, 0x7a, 0x93, 0x8f, 0xeb, 0xf5, 0xfe, 0xc1, 0x3b, 0xac, 0xfb, 0x16, 0xae, 0x10, 0xec, 0xbc, 0x4c, 0xbd, 0xcf}},
        evmc_address{.bytes = {0x97, 0xfe, 0xad, 0xcf, 0x4d, 0xd8, 0xd5, 0x8f, 0x35, 0xbe, 0x88, 0x6e, 0x3d, 0x62, 0xbe, 0x3b, 0xc2, 0xb1, 0xe7, 0xc1}},
        evmc_address{.bytes = {0x71, 0x2d, 0x91, 0x70, 0xa0, 0xf4, 0xe9, 0xf4, 0xab, 0x99, 0xa7, 0xf3, 0x74, 0xdb, 0xba, 0x3a, 0x56, 0x42, 0x0d, 0xb8}},
        evmc_address{.bytes = {0x5f, 0x68, 0x36, 0x65, 0xca, 0x87, 0xdb, 0xc3, 0xd1, 0x35, 0x89, 0x13, 0xda, 0x80, 0xe3, 0xc7, 0x1c, 0x32, 0x8f, 0xb0}},
        evmc_address{.bytes = {0xce, 0xca, 0x73, 0x67, 0x6b, 0x6b, 0xfe, 0xd2, 0xd7, 0x67, 0x3d, 0x13, 0x12, 0x01, 0xf7, 0x33, 0xf8, 0x4b, 0x51, 0xdf}},
        evmc_address{.bytes = {0x7a, 0x25, 0x0d, 0x56, 0x30, 0xb4, 0xcf, 0x53, 0x97, 0x39, 0xdf, 0x2c, 0x5d, 0xac, 0xb4, 0xc6, 0x59, 0xf2, 0x48, 0x8d}},
        evmc_address{.bytes = {0xda, 0xc1, 0x7f, 0x95, 0x8d, 0x2e, 0xe5, 0x23, 0xa2, 0x20, 0x62, 0x06, 0x99, 0x45, 0x97, 0xc1, 0x3d, 0x83, 0x1e, 0xc7}},
        evmc_address{.bytes = {0xb2, 0xec, 0xfe, 0x4e, 0x4d, 0x61, 0xf8, 0x79, 0x0b, 0xbb, 0x9d, 0xe2, 0xd1, 0x25, 0x9b, 0x9e, 0x24, 0x10, 0xce, 0xa5}},
        evmc_address{.bytes = {0xca, 0xf2, 0xeb, 0x49, 0x1d, 0x3b, 0xcd, 0x70, 0x2e, 0x7e, 0xd3, 0x3e, 0x9b, 0xe8, 0x63, 0xf7, 0xc1, 0xe7, 0x25, 0x82}},
        evmc_address{.bytes = {0x75, 0x7a, 0x19, 0x7b, 0x3b, 0x17, 0xb2, 0x07, 0xd6, 0xde, 0x38, 0x40, 0xde, 0x09, 0xbc, 0xf2, 0xdf, 0xb7, 0x5b, 0x72}},
        evmc_address{.bytes = {0xb7, 0x77, 0xeb, 0x03, 0x35, 0x57, 0x49, 0x0a, 0xbb, 0x7f, 0xb8, 0xf3, 0x94, 0x80, 0x00, 0x82, 0x64, 0x23, 0xea, 0x07}},
        evmc_address{.bytes = {0x3f, 0xc9, 0x1a, 0x3a, 0xfd, 0x70, 0x39, 0x5c, 0xd4, 0x96, 0xc6, 0x47, 0xd5, 0xa6, 0xcc, 0x9d, 0x4b, 0x2b, 0x7f, 0xad}}
    };
    for (auto& x : specials) {
        if (a == x) return true;
    }
    return false;
}
#endif

# if 0
static tbb::concurrent_queue<std::chrono::duration<int64_t, std::nano>> times;
static std::atomic<size_t> count;
static std::atomic<bool> is_running;

static void log_average(auto start_time, auto end_time) {
    times.push(end_time - start_time);
    size_t n = count.fetch_add(1) + 1;

    static constexpr size_t N = 10000;
    if (n % N == 0) {
        int64_t total = 0;
        for (size_t i = 0; i < N; ++i) {
            std::chrono::duration<int64_t, std::nano> t;
            bool b = times.try_pop(t);
            MONAD_ASSERT(b);
            total += t.count();
        }
        int64_t avg = total / N;
        std::cout << ">>>>>>>>>>>>>>>>>>>>> avg runtime of " << N << " messages was: " << avg << " ns <<<<<<<<<<<<<<<<<<<<<<" << std::endl;
    }
}

static std::mutex printmtx;
#endif

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

    //bool special = is_special(msg.code_address);

    auto const &cost_table = evmone::baseline::get_baseline_cost_table(
        execution_state->rev, code_analysis.eof_header.version);

    evmone::VM vm{};

    #ifdef EVMONE_TRACING
        std::ostringstream trace_ostream;
        vm.add_tracer(evmone::create_instruction_tracer(trace_ostream));
    #endif

    //auto start_time = std::chrono::high_resolution_clock::now();

    auto const gas = evmone::baseline::monad_execute(
        vm.get_tracer(), msg.gas, *execution_state, cost_table, code_analysis);

    //auto end_time = std::chrono::high_resolution_clock::now();
#if 0
    if (special) {
        printmtx.lock();
        std::cout << "bytecode:\n";
        for (auto b : msg.code_address.bytes)
            std::cout << std::format("{:02x}", (int)b);
        std::cout << "\n=>\n";
        for (auto b : code_analysis.executable_code) {
            std::cout << std::format("{:02x}", (uint64_t)b);
        }
        std::cout << "\n\n" << std::endl;
        printmtx.unlock();
        log_average(start_time, end_time);
    }
#endif

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
    std::shared_ptr<CodeAnalysis> code_analysis, bytes32_t const &code_hash,
    MonadJitCompiler &jit)
{
    if (code_analysis->executable_code.empty()) {
        return evmc::Result{EVMC_SUCCESS, msg.gas};
    }

    //bool special = is_special(msg.code_address);

    if (code_analysis->native_contract_main() == nullptr) {
        auto c = code_analysis->post_increment_execution_count();
#if 0
        if ((c+1) % 1000 == 0) {
            for (auto b : msg.code_address.bytes)
                std::cout << std::format("{:02x}", (int)b);
            std::cout << " count = " << (c+1) << std::endl;
        }
        if (special) {
            jit.add_compile_job(msg.code_address, code_analysis);
            jit.debug_wait_for(msg.code_address);
        } else {
            return baseline_execute_evmone_nonempty(msg, rev, host, *code_analysis);
        }
#endif
        if (c == 9) {
            jit.add_compile_job(code_hash, code_analysis);
            jit.debug_wait_for(code_hash);
        } else {
            return baseline_execute_evmone_nonempty(msg, rev, host, *code_analysis);
        }
    }

    //auto start_time = std::chrono::high_resolution_clock::now();

    evmc_result result = jit.execute(msg, rev, host, *code_analysis);

    //auto end_time = std::chrono::high_resolution_clock::now();
#if 0
    if (special) {
        log_average(start_time, end_time);
    }
#endif

    //std::cout << "execution gas used: " << (msg.gas - result.gas_left) << std::endl;
    //std::cout << "execution gas left: " << result.gas_left << std::endl;

    return evmc::Result{result};
}
#endif // MONAD_JIT

evmc::Result baseline_execute(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    std::shared_ptr<CodeAnalysis> code_analysis, bytes32_t const &code_hash,
    MonadJitCompiler &jit)
{
    /*
    std::cout << "START baseline_execute address ";
    for (auto b : msg.code_address.bytes)
        printf("%02X", (int)b);
    std::cout << std::endl;

    if (msg.code_address.bytes[0] == 0x01 && msg.code_address.bytes[1] == 0x10 && msg.code_address.bytes[2] == 0xb8) {
        std::cout << "bytecode\n";
        for (unsigned b : code_analysis->executable_code) {
            std::cout << std::format("{:02x}", b);
        }
    }
    std::cout << std::endl;

    auto start_time = std::chrono::high_resolution_clock::now();
    */

#ifdef MONAD_JIT
    auto result = baseline_execute_monad_jit(
            msg, rev, host, code_analysis, code_hash, jit);
#else
    (void)jit;
    (void)code_hash;
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
    std::cout << '\n';
    //std::cout << "TIME: " << (end_time - start_time) << std::endl;

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
