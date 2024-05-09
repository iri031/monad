#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <evmc/evmc.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Db;
class ResultBuffer;

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block(
    Block &, Db &, BlockHashBuffer const &, fiber::PriorityPool &,
    ResultBuffer &);

Result<std::vector<Receipt>> execute_block(
    evmc_revision, Block &, Db &, BlockHashBuffer const &,
    fiber::PriorityPool &, ResultBuffer &);

MONAD_NAMESPACE_END
