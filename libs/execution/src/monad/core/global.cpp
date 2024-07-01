#include <monad/core/global.hpp>

#include <map>
#include <mutex>
#include <set>

MONAD_NAMESPACE_BEGIN

std::set<Address> empty_address{};
std::set<Address> address_cache{};

std::mutex mtx;

std::set<Address> empty_address_changed{};
std::set<Address> empty_address_unchanged{};

MONAD_NAMESPACE_END
