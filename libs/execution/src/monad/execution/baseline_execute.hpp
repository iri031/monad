#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

evmc::Result baseline_execute(
    evmc_message const &, evmc_revision, evmc::Host *, CodeAnalysis const &, uint64_t);
void print_call_logs();
void load_hash_map();
MONAD_NAMESPACE_END
