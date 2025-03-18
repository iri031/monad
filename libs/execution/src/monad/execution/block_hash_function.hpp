#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <cstdint>
#include <functional>

MONAD_NAMESPACE_BEGIN

using BlockHashFunction = std::function<bytes32_t(uint64_t)>;

MONAD_NAMESPACE_END
