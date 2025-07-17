#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <algorithm>
#include <memory>

MONAD_NAMESPACE_BEGIN

Address address_from_secpkey(byte_string_fixed<65> const &serialized_pubkey)
{
    Address eth_address{};
    MONAD_ASSERT(serialized_pubkey[0] == 4);
    byte_string_view view{serialized_pubkey.data() + 1, 64};
    auto const hash = keccak256(view);
    std::copy_n(hash.bytes + 12, sizeof(Address), eth_address.bytes);
    return eth_address;
}

secp256k1_context const *get_secp_context()
{
    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        secp_context(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);
    return secp_context.get();
}

MONAD_NAMESPACE_END