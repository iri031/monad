#include <monad/config.hpp>
#include <monad/core/global.hpp>

MONAD_NAMESPACE_BEGIN

uint64_t blk_num{0};
std::set<std::pair<Address, bytes32_t>> seen{};

uint64_t nonzero_unseen{0};
uint64_t nonzero_seen{0};
uint64_t zero_unseen{0};
uint64_t zero_seen{0};

MONAD_NAMESPACE_END
