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

#include <iostream>
#include <fstream>
#include <unordered_map>
#include <sstream>

namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN

struct PairHashCompare {
    static size_t hash(const std::pair<const uint8_t*, size_t>& key) {
        size_t hash_value = 0;
        for (size_t i = 0; i < key.second; ++i) {
            hash_value = hash_value * 31 + key.first[i];
        }
        return hash_value;
    }

    static bool equal(const std::pair<const uint8_t*, size_t>& lhs, const std::pair<const uint8_t*, size_t>& rhs) {
        if (lhs.second != rhs.second) {
            return false;
        }
        return std::equal(lhs.first, lhs.first + lhs.second, rhs.first);
    }
};

using CalldataMap = tbb::concurrent_hash_map<
    std::pair<const uint8_t*, size_t>, 
    size_t, 
    PairHashCompare
>;

using ContractTable = tbb::concurrent_hash_map<evmc::address, CalldataMap, tbb::tbb_hash_compare<evmc::address>>;

ContractTable callLogs;
const int CONTRACT_CALL_THRESHOLD = 5;

std::unordered_map<std::string, std::string> load_hash_map(const std::string& filename) {
    std::unordered_map<std::string, std::string> hash_map;
    std::ifstream file(filename);
    std::string line;
    while (std::getline(file, line)) {
        if (!line.empty() && line.back() == '\r') {
            line.pop_back();
        }
        std::istringstream iss(line);
        std::string address, hash;
        if (std::getline(iss, address, ',') && std::getline(iss, hash)) {
            if (!hash.empty() && hash.back() == '\r') {
                hash.pop_back();
            }
            hash_map[address] = hash;
        }
    }
    return hash_map;
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
        const auto itemIsNew = callLogs.insert(accessor, msg.code_address);
        if (itemIsNew) {
            CalldataMap calldata_map;
            CalldataMap::accessor calldata_accessor;
            calldata_map.insert(calldata_accessor, std::make_pair(msg.input_data, msg.input_size));
            calldata_accessor->second = 1;
            calldata_accessor.release();
            accessor->second = std::move(calldata_map);
        }
        else {
            CalldataMap::accessor calldata_accessor;
            auto& calldata_map = accessor->second;
            const auto calldata_key = std::make_pair(msg.input_data, msg.input_size);

            if (calldata_map.find(calldata_accessor, calldata_key)) {
                // Increment the counter if the entry exists
                calldata_accessor->second += 1;
            } else {
                // Insert a new entry mapping current CALLDATA to 1
                calldata_map.insert(calldata_accessor, calldata_key);
                calldata_accessor->second = 1;
            }
            calldata_accessor.release();
        }
        accessor.release();
    }

    return evmc::Result{result};
}

std::string to_hex_string(const uint8_t* data, size_t size) {
    std::ostringstream oss;
    for (size_t i = 0; i < size; ++i) {
        oss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(data[i]);
    }
    return oss.str();
}

void print_call_logs() {
    auto hash_map = load_hash_map("/home/abhishek/hashes_trimmed.txt");

    for (const auto& [contract_address, calldata_map] : callLogs) {
        std::string address_hex = to_hex_string(contract_address.bytes, sizeof(contract_address.bytes));
        auto it = hash_map.find(address_hex);
        if (it != hash_map.end()) {
            std::ofstream file("/home/abhishek/ssd_2tb/calllogs/" + it->second);
            for (const auto& [calldata_key, count] : calldata_map) {
                file << to_hex_string(calldata_key.first, calldata_key.second) << "," << count << std::endl;
            }
        }
        else {
            LOG_ERROR("Contract address not found in hash map: {}", address_hex);
        }
    }
    LOG_INFO("Hash map size: {}", hash_map.size());

}

MONAD_NAMESPACE_END
