#pragma once

#include <monad/config.hpp>
#include <monad/core/result.hpp>
#include <monad/vm/vm.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct MonadChain;
struct Db;
class BlockHashBufferFinalized;

namespace mpt
{
    class Db;
}

namespace fiber
{
    class PriorityPool;
}

Result<std::pair<uint64_t, uint64_t>> runloop_monad_live(
    MonadChain const &, std::filesystem::path const &, mpt::Db &, Db &,
    vm::VM &, BlockHashBufferFinalized &, fiber::PriorityPool &,
    sig_atomic_t const volatile &stop);

Result<std::pair<uint64_t, uint64_t>> runloop_monad_replay(
    MonadChain const &, std::filesystem::path const &, mpt::Db &, Db &,
    vm::VM &, BlockHashBufferFinalized &, fiber::PriorityPool &,
    uint64_t &block_num, uint64_t const end_block_num,
    sig_atomic_t const volatile &stop);

MONAD_NAMESPACE_END
