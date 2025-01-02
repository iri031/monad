#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <monad/db/db.hpp>

MONAD_NAMESPACE_BEGIN

void dump_contracts(Db &db, uint64_t threshold);

evmc::Result baseline_execute(
    evmc_message const &, evmc_revision, evmc::Host *, CodeAnalysis const &, uint64_t);

MONAD_NAMESPACE_END
