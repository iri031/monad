#pragma once

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/vm/vm.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct MonadChain;
struct Db;
class BlockHashBufferFinalized;

namespace mpt2
{
    class Db;
}

namespace fiber
{
    class PriorityPool;
}

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    MonadChain const &, std::filesystem::path const &, mpt2::Db &, Db &,
    vm::VM &, BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &,
    uint64_t, sig_atomic_t const volatile &);

MONAD_NAMESPACE_END
