#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/monad/staking/util/bls.hpp>

#include <algorithm>
#include <memory>

MONAD_NAMESPACE_BEGIN

Address address_from_bls_key(byte_string_fixed<96> const &serialized_pubkey)
{
    Address eth_address{};
    MONAD_ASSERT(
        (serialized_pubkey.data()[0] & 0x11100000) ==
        0); // no flags should be set.

    auto const hash = keccak256(to_byte_string_view(serialized_pubkey));
    std::copy_n(hash.bytes + 12, sizeof(Address), eth_address.bytes);
    return eth_address;
}

MONAD_NAMESPACE_END
