#include <monad/config.hpp>
#include <monad/core/global.hpp>

#include <map>
#include <set>

MONAD_NAMESPACE_BEGIN

uint64_t blk_num{0};
std::map<std::pair<Address, bytes32_t>, std::set<bytes32_t>> accessed{};
std::set<std::pair<Address, bytes32_t>> accessed_nonzero{};

uint64_t nonzero_unaccessed{0};
uint64_t nonzero_accessed{0};
uint64_t zero_unaccessed{0};
uint64_t zero_accessed{0};

MONAD_NAMESPACE_END
