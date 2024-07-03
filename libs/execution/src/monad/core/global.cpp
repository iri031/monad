#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/global.hpp>

#include <map>
#include <mutex>
#include <set>

MONAD_NAMESPACE_BEGIN

std::set<std::pair<Address, bytes32_t>> empty_storage{};
std::set<std::pair<Address, bytes32_t>> storage_cache{};

std::mutex mtx;

std::set<std::pair<Address, bytes32_t>> empty_storage_changed{};
std::set<std::pair<Address, bytes32_t>> empty_storage_unchanged{};

MONAD_NAMESPACE_END
