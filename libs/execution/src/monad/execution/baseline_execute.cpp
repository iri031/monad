#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/execution/baseline_execute.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmone/baseline.hpp>

#ifndef __clang__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored_attributes "clang::"
#endif
#include <evmone/execution_state.hpp>
#ifndef __clang__
    #pragma GCC diagnostic pop
#endif

#include <evmone/baseline.hpp>
#include <evmone/evmone.h>
#include <evmone/vm.hpp>

#ifdef EVMONE_TRACING
    #include <evmone/tracing.hpp>

    #include <quill/Quill.h>

    #include <sstream>
#endif

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <memory>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <tbb/concurrent_hash_map.h>
#include <monad/core/assert.h>
#include <filesystem>
#include <monad/core/keccak.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/fmt/address_fmt.hpp>
namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN

using ContractTable = tbb::concurrent_hash_map<evmc::address,uint64_t, tbb::tbb_hash_compare<evmc::address>>;

ContractTable call_counter;

std::shared_ptr<CodeAnalysis> read_code(Db &db, evmc::address addr)
{
    auto ac= db.read_account(addr);
    return db.read_code(ac->code_hash);
}

void dump_contract(evmc::address addr, std::string contracts_dir_var, Db &db)
{
    auto code_analysisp = read_code(db, addr);
    assert(code_analysisp);
    // content addressable path for the contract using keccak of the actual code
    auto const code_hash = keccak256(code_analysisp->executable_code);

    auto code_hash_dir = fs::path(contracts_dir_var) / "code_hash";
    fs::create_directories(code_hash_dir);

    auto contract_path =
        code_hash_dir /
        fmt::format(
            "{}", intx::hex(intx::be::load<intx::uint256>(code_hash.bytes)));

    auto os = std::ofstream(contract_path);
    os.write(
        reinterpret_cast<char const *>(code_analysisp->executable_code.data()),
        static_cast<std::streamsize>(code_analysisp->executable_code.size()));


    auto code_address_dir = fs::path(contracts_dir_var) / "code_address";

    fs::create_directories(code_address_dir);

    auto contract_address_path = code_address_dir / fmt::format("{}", addr);

    fs::create_symlink(contract_path, contract_address_path);
}

void dump_contracts(Db &db, uint64_t threshold){
    auto contracts_dir_var = std::getenv("CONTRACTS_DIR");
    MONAD_ASSERT(contracts_dir_var);
    for (auto const &addr : call_counter) {
        if (addr.second >= threshold) {
            dump_contract(addr.first, contracts_dir_var, db);
        }
    }
}


evmc::Result baseline_execute(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    CodeAnalysis const &code_analysis, uint64_t
    )
{
    std::unique_ptr<evmc_vm> const vm{evmc_create_evmone()};

    if (code_analysis.executable_code.empty()) {
        return evmc::Result{EVMC_SUCCESS, msg.gas};
    }

#ifdef EVMONE_TRACING
    std::ostringstream trace_ostream;
    static_cast<evmone::VM *>(vm.get())->add_tracer(
        evmone::create_instruction_tracer(trace_ostream));
#endif

    auto const execution_state = std::make_unique<evmone::ExecutionState>(
        msg,
        rev,
        host->get_interface(),
        host->to_context(),
        code_analysis.executable_code,
        byte_string_view{});

    auto const result = evmone::baseline::execute(
        *static_cast<evmone::VM *>(vm.get()),
        msg.gas,
        *execution_state,
        code_analysis);

#ifdef EVMONE_TRACING
    LOG_TRACE_L1("{}", trace_ostream.str());
#endif

    if (result.status_code == EVMC_SUCCESS) {
        ContractTable::accessor accessor;
        const auto itemIsNew = call_counter.insert( accessor, msg.code_address );
        if (itemIsNew) {
            accessor->second = 1;
        }
        else {
            accessor->second = accessor->second + 1;
        }
        accessor.release();
    }

    return evmc::Result{result};
}

MONAD_NAMESPACE_END
