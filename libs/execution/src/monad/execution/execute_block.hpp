#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/staticanalysis/expr.hpp>
#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct ExecutionResult;

struct CalleePredInfo {
    std::unordered_map<Address, bytes32_t> code_hashes;
    ExpressionPool epool;
    std::map<evmc::bytes32, std::vector<uint32_t>> callees;
    std::optional<std::vector<uint32_t>*> lookup_callee(evmc::address runningAddress) {
        bytes32_t code_hash = code_hashes[runningAddress];
        auto it = callees.find(code_hash);
        if(it == callees.end()) {
            return std::nullopt;
        }
        return &(it->second);
    }
};

inline intx::uint256 ofBoost(const Word256& word) {
    uint64_t words[4];
    to_uint64_array(word, words);

    // Construct intx::uint256 from the uint64_t array
    intx::uint256 result{words[0], words[1], words[2], words[3]};

    // For debugging: log the Word256 and the intx::uint256 values
    //LOG_INFO("Converting Word256 to intx::uint256");
    // LOG_INFO("Word256:       0x{}", word.str(0, std::ios_base::hex));
    //LOG_INFO("intx::uint256: 0x{}", intx::to_string(result, 16));

    return result;
}

inline evmc::address get_address(const Word256& word) {
    auto truncated = intx::be::trunc<evmc::address>(ofBoost(word));
    return truncated;
}

inline evmc::address get_address(uint32_t index, ExpressionPool &epool) {
    Word256 word = epool.getConst(index);
    return get_address(word);
}

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, BlockState &, BlockHashBuffer const &,
    fiber::PriorityPool &, CalleePredInfo &);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &, CalleePredInfo &);

MONAD_NAMESPACE_END
