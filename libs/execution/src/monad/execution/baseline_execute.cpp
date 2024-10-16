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

typedef tbb::concurrent_hash_map<evmc::address,int, tbb::tbb_hash_compare<evmc::address>> ContractTable;
typedef tbb::concurrent_hash_map<evmc::address,int, tbb::tbb_hash_compare<evmc::address>>::accessor Accessor;

ContractTable call_counter;
const int CONTRACT_CALL_THRESHOLD = 5;


evmc::Result baseline_execute(
    evmc_message const &msg, evmc_revision const rev, evmc::Host *const host,
    CodeAnalysis const &code_analysis)
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
        Accessor accessor;
        const auto itemIsNew = call_counter.insert( accessor, msg.code_address );
        if (itemIsNew) {
            accessor->second = 1;
        }
        else {
            const int call_count = accessor->second;
            if (call_count != -1) {
                if (call_count > CONTRACT_CALL_THRESHOLD) {
                    // mark for insertion into the contracts dump
                    accessor->second = -1;
                    auto contracts_dir_var = std::getenv("CONTRACTS_DIR");
                    MONAD_ASSERT(contracts_dir_var);

                    // content addressable path for the contract using keccak of the actual code
                    auto const code_hash = keccak256(code_analysis.executable_code);

                    auto code_hash_dir = fs::path(contracts_dir_var) / "code_hash" /
                            fmt::format("{:02x}", code_hash.bytes[0]) /
                            fmt::format("{:02x}", code_hash.bytes[1]);

                    fs::create_directories(code_hash_dir);

                    auto contract_path = code_hash_dir / fmt::format("{}", intx::hex(intx::be::load<intx::uint256>(code_hash.bytes)));

                    auto os = std::ofstream(contract_path);
                    os.write(
                        reinterpret_cast<char const *>(code_analysis.executable_code.data()),
                        code_analysis.executable_code.size());

                    auto code_address_dir = fs::path(contracts_dir_var) / "code_address" /
                            fmt::format("{:02x}", msg.code_address.bytes[0]) /
                            fmt::format("{:02x}", msg.code_address.bytes[1]);

                    fs::create_directories(code_address_dir);

                    const Address& addr = msg.code_address;
                    auto contract_address_path = code_address_dir / fmt::format("{}", addr);

                    fs::create_symlink(contract_path, contract_address_path);
                } 
                else {
                    accessor->second = call_count + 1;
                }
            }
        }
        accessor.release();
    }

    return evmc::Result{result};
}

MONAD_NAMESPACE_END
