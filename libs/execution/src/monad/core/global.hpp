#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <set>

MONAD_NAMESPACE_BEGIN

extern uint64_t blk_num;
extern std::set<std::pair<Address, bytes32_t>> accessed;

extern uint64_t nonzero_unaccessed;
extern uint64_t nonzero_accessed;
extern uint64_t zero_unaccessed;
extern uint64_t zero_accessed;

MONAD_NAMESPACE_END
