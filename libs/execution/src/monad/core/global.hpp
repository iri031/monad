#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <map>
#include <mutex>
#include <set>

MONAD_NAMESPACE_BEGIN

extern std::set<Address> empty_address;
extern std::set<Address> address_cache;

extern std::mutex mtx;

extern std::set<Address> empty_address_changed;
extern std::set<Address> empty_address_unchanged;

MONAD_NAMESPACE_END
