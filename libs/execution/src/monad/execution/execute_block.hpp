#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/block_hash_function.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockState;
struct ExecutionResult;

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, BlockState &, BlockHashFunction const &,
    fiber::PriorityPool &);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, BlockState &,
    BlockHashFunction const &, fiber::PriorityPool &);

MONAD_NAMESPACE_END
