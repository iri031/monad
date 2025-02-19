#pragma once

#include <monad/config.hpp>
#include <monad/core/result.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct Chain;
struct Db;
class BlockHashBuffer;

namespace mpt
{
    class Db;
}

namespace fiber
{
    class PriorityPool;
}

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    Chain const &, std::filesystem::path const &, mpt::Db &, Db &,
    BlockHashBuffer const &, fiber::PriorityPool &, uint64_t &, uint64_t,
    sig_atomic_t const volatile &);

MONAD_NAMESPACE_END
