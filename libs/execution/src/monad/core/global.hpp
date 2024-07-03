#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <map>
#include <mutex>
#include <set>

MONAD_NAMESPACE_BEGIN

extern std::set<std::pair<Address, bytes32_t>> empty_storage;
extern std::set<std::pair<Address, bytes32_t>> storage_cache;

extern std::mutex mtx;

extern std::set<std::pair<Address, bytes32_t>> empty_storage_changed;
extern std::set<std::pair<Address, bytes32_t>> empty_storage_unchanged;

MONAD_NAMESPACE_END
