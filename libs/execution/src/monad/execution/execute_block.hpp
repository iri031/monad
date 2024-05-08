#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <evmc/evmc.h>

#include <map>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Db;
enum class AccessOp;

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block(
    Block &, Db &, BlockHashBuffer const &, fiber::PriorityPool &,
    std::map<Address, std::map<bytes32_t, std::vector<AccessOp>>>
        &storage_accesses);

Result<std::vector<Receipt>> execute_block(
    evmc_revision, Block &, Db &, BlockHashBuffer const &,
    fiber::PriorityPool &,
    std::map<Address, std::map<bytes32_t, std::vector<AccessOp>>>
        &storage_accesses);

MONAD_NAMESPACE_END
