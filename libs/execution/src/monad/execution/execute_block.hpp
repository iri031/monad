#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/staticanalysis/expr.hpp>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>


#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct ExecutionResult;

struct CalleePredInfo {
    std::unordered_map<Address, bytes32_t> code_hashes;
    ExpressionPool epool;
    std::unordered_map<evmc::bytes32, Prediction> predictions;
    std::optional<Prediction*> lookup_callee(evmc::address runningAddress) {
        bytes32_t code_hash = code_hashes[runningAddress];
        //LOG_INFO("code_hash: {}, runningAddress: {}", code_hash, runningAddress);
        auto it = predictions.find(code_hash);
        if(it == predictions.end()) {
            return std::nullopt;
        }
        return &(it->second);
    }
};

uint64_t numPredictedFootprints();
uint64_t numTTPredictedFootprints();
std::chrono::duration<double> get_compile_footprints_time();
std::chrono::duration<double> get_footprint_time();

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, BlockState &, BlockHashBuffer const &,
    fiber::PriorityPool &, CalleePredInfo &);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &, CalleePredInfo &);

MONAD_NAMESPACE_END
