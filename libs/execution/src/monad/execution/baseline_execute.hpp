#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/execution/code_analysis.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

class MonadJitCompiler;

evmc::Result baseline_execute(
    evmc_message const &, evmc_revision, evmc::Host *,
    std::shared_ptr<CodeAnalysis>, MonadJitCompiler &);

evmc::Result baseline_execute_evmone(
    evmc_message const &, evmc_revision, evmc::Host *,
    ::evmone::baseline::CodeAnalysis const &);

evmc::Result baseline_execute_monad_jit(
    bool *, evmc_message const &, evmc_revision, evmc::Host *,
    std::shared_ptr<CodeAnalysis>, MonadJitCompiler &);

MONAD_NAMESPACE_END
