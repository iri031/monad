#pragma once

#include <monad/chain/monad_revision.h>
#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/execution/precompiles.hpp>

#include <evmc/evmc.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

class State;

constexpr Address MAX_RESERVE_BALANCE_ADDRESS =
    0xff00000000000000000000000000000000000001_address;

uint64_t max_reserve_balance_cost(monad_revision, byte_string_view);

// Set max reserve balance of sender and return what it was before
// Get max reserve balance of any address
PrecompileResult
max_reserve_balance_execute(Address const &sender, byte_string_view, State &);

std::optional<evmc::Result>
check_call_monad_precompile(monad_revision, evmc_message const &, State &);

MONAD_NAMESPACE_END
