#include <monad/config.hpp>
#include <monad/core/global.hpp>

MONAD_NAMESPACE_BEGIN

uint64_t blk_num{0};
std::set<std::pair<Address, bytes32_t>> accessed{};

uint64_t nonzero_unaccessed{0};
uint64_t nonzero_accessed{0};
uint64_t zero_unaccessed{0};
uint64_t zero_accessed{0};

MONAD_NAMESPACE_END
