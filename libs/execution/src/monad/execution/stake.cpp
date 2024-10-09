#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.hpp>
#include <monad/execution/deposit.hpp>
#include <monad/execution/stake.hpp>

#include <bit>

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr size_t PUBKEY_SIZE = 48;
    constexpr size_t WITHDRAWAL_CREDENTIALS_SIZE = 32;
    constexpr size_t SIGNATURE_SIZE = 96;

    template <size_t N>
    using ByteSpan = std::span<unsigned char const, N>;

    bool stake_deposit(
        ByteSpan<PUBKEY_SIZE> const pubkey,
        ByteSpan<WITHDRAWAL_CREDENTIALS_SIZE> const withdrawal_credentials,
        uint256_t const &amount, ByteSpan<SIGNATURE_SIZE> const signature,
        State &state)
    {
    }
}

uint64_t stake_cost(evmc_message const &, State &)
{
    return 0;
}

// key keccak256([pubkey, type])

// type
//   0 active               pubkey [0:31]
//   1 active               pubkey [31:47]
//   2 active               [withdrawal_addr, amount]
//   3 pending              deposit
//   4 pending              withdrawal
//   5 update               deposit
//   6 update               withdrawal

// 0...0, 0...1, 0...2
// 1...0, 1...1, 1...2
// 2...0, 2...1, 2...2

// 1  - actions: deposit, withdraw, etc.
// 48 - pubkey
// 20 - withdrawal_addr
// 96 - signature
// 8  - withdrawal amount, Gwei, in big endian (optional)
// 32 - checksum (keccak)
StakeError stake_run(evmc_message const &msg, State &state)
{
    constexpr size_t deposit_size = 1 + PUBKEY_SIZE +
                                    WITHDRAWAL_CREDENTIALS_SIZE +
                                    SIGNATURE_SIZE + sizeof(hash256);
    constexpr size_t withdrawal_size = deposit_size + sizeof(uint64_t);

    if (msg.input_data == nullptr || msg.input_size == 0) {
        return StakeError::InvalidArgs;
    }
    else if (*msg.input_data == 0) {
        if (msg.input_size != deposit_size) {
            return StakeError::InvalidArgs;
        }
    }
    else if (*msg.input_data == 1) {
        if (msg.input_size != withdrawal_size) {
            return StakeError::InvalidArgs;
        }
    }
    else {
        return StakeError::InvalidArgs;
    }

    byte_string_view const data{msg.input_data, msg.input_size};
    auto const cksum = keccak256(data.substr(0, data.size() - sizeof(hash256)));
    if (!data.ends_with(to_byte_string_view(cksum.str))) {
        return StakeError::BadChecksum;
    }
}

MONAD_NAMESPACE_END
