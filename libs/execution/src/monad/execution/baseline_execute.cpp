#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/execution/baseline_execute.hpp>
#include <monad/execution/code_analysis.hpp>

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

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/loader.h>

#include <memory>

MONAD_NAMESPACE_BEGIN

evmc::Result baseline_execute(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    CodeAnalysis const &code_analysis)
{
    if (code_analysis.executable_code.empty()) {
        return evmc::Result{EVMC_SUCCESS, msg.gas};
    }

#if 0
#ifdef EVMONE_TRACING
    std::ostringstream trace_ostream;
    vm.add_tracer(evmone::create_instruction_tracer(trace_ostream));
#endif

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

    if (MONAD_UNLIKELY(vm.get_tracer() != nullptr)) {
        vm.get_tracer()->notify_execution_end(result);
    }

    #ifdef EVMONE_TRACING
        LOG_TRACE_L1("{}", trace_ostream.str());
    #endif

    return evmc::Result{result};
#else
    evmc_loader_error_code ec = EVMC_LOADER_UNSPECIFIED_ERROR;
    evmc::VM vm{evmc_load_and_configure(
        "/home/andreaslyn/monad/monad-jit/target/debug/libmonad_nevm_vm.so", &ec)};
    MONAD_ASSERT(ec == EVMC_LOADER_SUCCESS);
    evmc::Result result = vm.execute(*host, rev, msg,
        code_analysis.executable_code.data(), code_analysis.executable_code.size());

    return result;
#endif
}

MONAD_NAMESPACE_END
