#pragma once

#include <monad/config.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

class State;

enum class StakeError
{
    Success = 0,
    BadChecksum,
    BadPubkey,
    InvalidArgs,
};

uint64_t stake_cost(evmc_message const &, State &);

StakeError stake_run(evmc_message const &, State &);

MONAD_NAMESPACE_END
