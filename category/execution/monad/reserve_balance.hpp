#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>

#include <ankerl/unordered_dense.h>

MONAD_NAMESPACE_BEGIN

struct GasFees
{
    ankerl::unordered_dense::segmented_map<Address, uint256_t> const
        &grandparent_gas_fees;
    ankerl::unordered_dense::segmented_map<Address, uint256_t> const
        &parent_gas_fees;
    std::vector<std::pair<Address, uint256_t>> const &gas_fees;
};

struct Authorities
{
    ankerl::unordered_dense::segmented_set<Address> const
        &grandparent_authorities;
    ankerl::unordered_dense::segmented_set<Address> const &parent_authorities;
    std::vector<std::vector<std::optional<Address>>> const &authorities;
};

bool can_dip_into_reserve(
    uint64_t const i, GasFees const &gas_fees,
    ankerl::unordered_dense::segmented_set<Address> const
        &delegated_k_blocks_ago,
    Authorities const &authorities)
{
    MONAD_ASSERT(i < authorities.authorities.size());

    Address const &sender = gas_fees.gas_fees[i].first;

    if (delegated_k_blocks_ago.contains(sender)) {
        return false;
    }

    // check historical block senders and authorities
    for (ankerl::unordered_dense::segmented_map<Address, uint256_t> const &
             fees : {gas_fees.grandparent_gas_fees, gas_fees.parent_gas_fees}) {
        if (fees.contains(sender)) {
            return false;
        }
    }

    for (ankerl::unordered_dense::segmented_set<Address> const &auths :
         {authorities.grandparent_authorities,
          authorities.parent_authorities}) {
        if (auths.contains(sender)) {
            return false;
        }
    }

    // check current senders and authorities
    for (uint64_t j = 0; j < i; ++j) {
        if (sender == gas_fees.gas_fees[j].first) {
            return false;
        }
        if (std::ranges::contains(authorities.authorities[j], sender)) {
            return false;
        }
    }

    return true;
}

bool validate_transaction(
    uint64_t const i, GasFees const &gas_fees,
    ankerl::unordered_dense::segmented_map<Address, uint256_t> const
        &balances_k_blocks_ago,
    ankerl::unordered_dense::segmented_set<Address> const
        &delegated_k_blocks_ago,
    Authorities const &authorities)
{
    constexpr uint256_t DEFAULT_RESERVE = uint256_t{100} * 1000000000000000000;
    auto const &[grandparent_gas_fees, parent_gas_fees, current_gas_fees] =
        gas_fees;

    MONAD_ASSERT(i < current_gas_fees.size());

    Address const &sender = gas_fees.gas_fees[i].first;
    uint256_t const pending_fees = [&] {
        uint256_t ret = 0;
        if (grandparent_gas_fees.contains(sender)) {
            ret += grandparent_gas_fees.at(sender);
        }
        if (parent_gas_fees.contains(sender)) {
            ret += parent_gas_fees.at(sender);
        }
        for (unsigned j = 0; j < i; ++j) {
            if (sender == current_gas_fees[j].first) {
                ret += current_gas_fees[j].second;
            }
        }
        return ret;
    }();
    uint256_t const delayed_balance = balances_k_blocks_ago.contains(sender)
                                          ? balances_k_blocks_ago.at(sender)
                                          : 0;
    MONAD_ASSERT(delayed_balance >= pending_fees);

    if (can_dip_into_reserve(
            i, gas_fees, delegated_k_blocks_ago, authorities)) {
        uint256_t const available_balance = delayed_balance - pending_fees;
        return current_gas_fees[i].second <= available_balance;
    }

    uint256_t const reserve = std::min(delayed_balance, DEFAULT_RESERVE);
    MONAD_ASSERT(reserve >= pending_fees);
    uint256_t const available_balance = reserve - pending_fees;
    return current_gas_fees[i].second <= available_balance;
}

MONAD_NAMESPACE_END
