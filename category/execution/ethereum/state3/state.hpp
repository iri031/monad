// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/version_stack.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>

#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <bit>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State
{
    template <typename K, typename V>
    using Map = ankerl::unordered_dense::segmented_map<K, V>;

    BlockState &block_state_;

    Incarnation const incarnation_;

    Map<Address, AccountState> original_{};

    Map<Address, VersionStack<AccountState>> current_{};

    VersionStack<std::vector<Receipt::Log>> logs_{{}};

    Map<bytes32_t, vm::SharedVarcode> code_{};

    unsigned version_{0};

    AccountState &original_account_state(Address const &address)
    {
        auto it = original_.find(address);
        if (it == original_.end()) {
            // block state
            auto const account = block_state_.read_account(address);
            it = original_.try_emplace(address, account).first;
        }
        return it->second;
    }

    AccountState const &recent_account_state(Address const &address)
    {
        // current
        auto const it = current_.find(address);
        if (it != current_.end()) {
            return it->second.recent();
        }
        // original
        return original_account_state(address);
    }

    AccountState &current_account_state(Address const &address)
    {
        // current
        auto it = current_.find(address);
        if (MONAD_UNLIKELY(it == current_.end())) {
            // original
            auto const &account_state = original_account_state(address);
            it = current_.try_emplace(address, account_state, version_).first;
        }
        return it->second.current(version_);
    }

    std::optional<Account> &current_account(Address const &address)
    {
        return current_account_state(address).account_;
    }

    friend class BlockState; // TODO

public:
    State(BlockState &block_state, Incarnation const incarnation)
        : block_state_{block_state}
        , incarnation_{incarnation}
    {
    }

    State(State &&) = default;
    State(State const &) = delete;
    State &operator=(State &&) = delete;
    State &operator=(State const &) = delete;

    Map<Address, AccountState> const &original() const
    {
        return original_;
    }

    Map<Address, VersionStack<AccountState>> const &current() const
    {
        return current_;
    }

    void push()
    {
        ++version_;
    }

    void pop_accept()
    {
        MONAD_ASSERT(version_);

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            it->second.pop_accept(version_);
        }

        logs_.pop_accept(version_);

        --version_;
    }

    void pop_reject()
    {
        MONAD_ASSERT(version_);

        std::vector<Address> removals;

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            if (it->second.pop_reject(version_)) {
                removals.push_back(it->first);
            }
        }

        logs_.pop_reject(version_);

        while (removals.size()) {
            current_.erase(removals.back());
            removals.pop_back();
        }

        --version_;
    }

    ////////////////////////////////////////

    vm::VM &vm()
    {
        return block_state_.vm();
    }

    std::optional<Account> const &recent_account(Address const &address)
    {
        return recent_account_state(address).account_;
    }

    void set_original_nonce(Address const &address, uint64_t const nonce)
    {
        auto &account_state = original_account_state(address);
        auto &account = account_state.account_;
        if (!account.has_value()) {
            account = Account{};
        }
        account->nonce = nonce;
    }

    ////////////////////////////////////////

    bool account_exists(Address const &address)
    {
        return recent_account(address).has_value();
    }

    bool account_is_dead(Address const &address)
    {
        return is_dead(recent_account(address));
    }

    uint64_t get_nonce(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0;
    }

    bytes32_t get_balance(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return intx::be::store<bytes32_t>(account.value().balance);
        }
        return {};
    }

    bytes32_t get_code_hash(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    bytes32_t get_storage(Address const &address, bytes32_t const &key)
    {
        auto const it = current_.find(address);
        if (it == current_.end()) {
            auto const it2 = original_.find(address);
            MONAD_ASSERT(it2 != original_.end());
            auto &account_state = it2->second;
            auto const &account = account_state.account_;
            MONAD_ASSERT(account.has_value());
            auto &storage = account_state.storage_;
            auto it3 = storage.find(key);
            if (it3 == storage.end()) {
                bytes32_t const value = block_state_.read_storage(
                    address, account.value().incarnation, key);
                it3 = storage.try_emplace(key, value).first;
            }
            return it3->second;
        }
        else {
            auto const &account_state = it->second.recent();
            auto const &account = account_state.account_;
            MONAD_ASSERT(account.has_value());
            auto const &storage = account_state.storage_;
            if (auto const it2 = storage.find(key); it2 != storage.end()) {
                return it2->second;
            }
            auto const it2 = original_.find(address);
            MONAD_ASSERT(it2 != original_.end());
            auto &original_account_state = it2->second;
            auto const &original_account = original_account_state.account_;
            if (!original_account.has_value() ||
                account.value().incarnation !=
                    original_account.value().incarnation) {
                return {};
            }
            auto &original_storage = original_account_state.storage_;
            auto it3 = original_storage.find(key);
            if (it3 == original_storage.end()) {
                bytes32_t const value = block_state_.read_storage(
                    address, account.value().incarnation, key);
                it3 = original_storage.try_emplace(key, value).first;
            }
            return it3->second;
        }
    }

    bytes32_t
    get_transient_storage(Address const &address, bytes32_t const &key)
    {
        return recent_account_state(address).get_transient_storage(key);
    }

    bool is_touched(Address const &address)
    {
        auto const &account_state = recent_account_state(address);
        return account_state.is_touched();
    }

    ////////////////////////////////////////

    void set_nonce(Address const &address, uint64_t const nonce)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }
        account.value().nonce = nonce;
    }

    void add_to_balance(Address const &address, uint256_t const &delta)
    {
        auto &account_state = current_account_state(address);
        auto &account = account_state.account_;
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }

        MONAD_ASSERT(
            std::numeric_limits<uint256_t>::max() - delta >=
            account.value().balance);

        account.value().balance += delta;
        account_state.touch();
    }

    void subtract_from_balance(Address const &address, uint256_t const &delta)
    {
        auto &account_state = current_account_state(address);
        auto &account = account_state.account_;
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }

        MONAD_ASSERT(delta <= account.value().balance);

        account.value().balance -= delta;
        account_state.touch();
    }

    void set_code_hash(Address const &address, bytes32_t const &hash)
    {
        auto &account = current_account(address);
        MONAD_ASSERT(account.has_value());
        account.value().code_hash = hash;
    }

    evmc_storage_status set_storage(
        Address const &address, bytes32_t const &key, bytes32_t const &value)
    {
        bytes32_t original_value;
        auto &account_state = current_account_state(address);
        MONAD_ASSERT(account_state.account_);
        // original
        {
            auto &orig_account_state = original_account_state(address);
            auto &storage = orig_account_state.storage_;
            auto it = storage.find(key);
            if (it == storage.end()) {
                Incarnation const incarnation =
                    account_state.account_->incarnation;
                bytes32_t const value =
                    block_state_.read_storage(address, incarnation, key);
                it = storage.try_emplace(key, value).first;
            }
            original_value = it->second;
        }
        // state
        {
            auto const result =
                account_state.set_storage(key, value, original_value);
            return result;
        }
    }

    void set_transient_storage(
        Address const &address, bytes32_t const &key, bytes32_t const &value)
    {
        current_account_state(address).set_transient_storage(key, value);
    }

    void touch(Address const &address)
    {
        auto &account_state = current_account_state(address);
        account_state.touch();
    }

    evmc_access_status access_account(Address const &address)
    {
        auto &account_state = current_account_state(address);
        return account_state.access();
    }

    evmc_access_status
    access_storage(Address const &address, bytes32_t const &key)
    {
        auto &account_state = current_account_state(address);
        return account_state.access_storage(key);
    }

    ////////////////////////////////////////

    template <evmc_revision rev>
    bool selfdestruct(Address const &address, Address const &beneficiary)
    {
        auto &account_state = current_account_state(address);
        auto &account = account_state.account_;
        MONAD_ASSERT(account.has_value());

        if constexpr (rev < EVMC_CANCUN) {
            add_to_balance(beneficiary, account.value().balance);
            account.value().balance = 0;
        }
        else {
            if (address != beneficiary ||
                account->incarnation == incarnation_) {
                add_to_balance(beneficiary, account.value().balance);
                account.value().balance = 0;
            }
        }

        return account_state.destruct();
    }

    // YP (87)
    template <evmc_revision rev>
    void destruct_suicides()
    {
        MONAD_ASSERT(!version_);

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            auto &stack = it->second;
            MONAD_ASSERT(stack.size() == 1);
            MONAD_ASSERT(stack.version() == 0);
            auto &account_state = stack.current(0);
            if (account_state.is_destructed()) {
                auto &account = account_state.account_;
                if constexpr (rev < EVMC_CANCUN) {
                    account.reset();
                }
                else {
                    if (account->incarnation == incarnation_) {
                        account.reset();
                    }
                }
            }
        }
    }

    // YP (88)
    void destruct_touched_dead()
    {
        MONAD_ASSERT(!version_);

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            auto &stack = it->second;
            MONAD_ASSERT(stack.size() == 1);
            MONAD_ASSERT(stack.version() == 0);
            auto &account_state = stack.current(0);
            if (MONAD_LIKELY(!account_state.is_touched())) {
                continue;
            }
            auto &account = account_state.account_;
            if (is_dead(account)) {
                account.reset();
            }
        }
    }

    ////////////////////////////////////////

    vm::SharedVarcode read_code(bytes32_t const &code_hash)
    {
        {
            auto const it = code_.find(code_hash);
            if (it != code_.end()) {
                return it->second;
            }
        }
        return block_state_.read_code(code_hash);
    }

    vm::SharedVarcode get_code(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return block_state_.read_code(NULL_HASH);
        }
        return read_code(account.value().code_hash);
    }

    size_t get_code_size(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return 0;
        }
        bytes32_t const &code_hash = account.value().code_hash;
        {
            auto const it = code_.find(code_hash);
            if (it != code_.end()) {
                auto const &vcode = it->second;
                MONAD_ASSERT(vcode);
                return vcode->intercode()->code_size();
            }
        }
        auto const vcode = block_state_.read_code(code_hash);
        MONAD_ASSERT(vcode);
        return vcode->intercode()->code_size();
    }

    size_t copy_code(
        Address const &address, size_t const offset, uint8_t *const buffer,
        size_t const buffer_size)
    {
        auto const &account = recent_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return 0;
        }
        bytes32_t const &code_hash = account.value().code_hash;
        vm::SharedVarcode vcode{};
        {
            auto const it = code_.find(code_hash);
            if (it != code_.end()) {
                vcode = it->second;
            }
            else {
                vcode = block_state_.read_code(code_hash);
            }
        }
        MONAD_ASSERT(vcode);
        auto const &icode = vcode->intercode();
        auto const code_size = icode->code_size();
        if (offset > code_size) {
            return 0;
        }
        auto const n = std::min(code_size - offset, buffer_size);
        std::copy_n(icode->code() + offset, n, buffer);
        return n;
    }

    void set_code(Address const &address, byte_string_view const code)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return;
        }

        auto const code_hash = to_bytes(keccak256(code));
        code_[code_hash] =
            vm().try_insert_varcode(code_hash, vm::make_shared_intercode(code));
        account.value().code_hash = code_hash;
    }

    ////////////////////////////////////////

    void create_contract(Address const &address)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(account.has_value())) {
            // EIP-684
            MONAD_ASSERT(account->nonce == 0);
            MONAD_ASSERT(account->code_hash == NULL_HASH);
            // keep the balance, per chapter 7 of the YP
            account->incarnation = incarnation_;
        }
        else {
            account = Account{.incarnation = incarnation_};
        }
    }

    ////////////////////////////////////////

    std::vector<Receipt::Log> const &logs()
    {
        return logs_.recent();
    }

    void store_log(Receipt::Log const &log)
    {
        auto &logs = logs_.current(version_);
        logs.push_back(log);
    }

    ////////////////////////////////////////

    void set_to_state_incarnation(Address const &address)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }
        account.value().incarnation = incarnation_;
    }

    // The "account size" of the state is the number of entries in the
    // `Address -> AccountState` prestate mapping
    size_t get_account_size() const
    {
        return size(original_);
    }

    // Given how original_ and current_ are formed, it is the case that
    // KEYS(current_) is a subset of KEYS(original_); this implies that to
    // visit all reads and writes of state data, we can walk the original_
    // key-value pairs. For each key in original_, if it also exists in
    // current_, then this account's state was also modified somehow (subject
    // to an A -> B -> A problem). To avoid exposing the internals, the user
    // passes a visitor which visits address, prestate, and modified state.
    // Modified state will be set to nullptr if the account wasn't modified.
    template <std::invocable<
        Address const *, AccountState const *, AccountState const *>
                  F>
    void visit_accounts(F &&f) const
    {
        for (auto const &[address, original_state] : original_) {
            AccountState const *current_state = nullptr;
            if (auto const i = current_.find(address); i != end(current_)) {
                current_state = std::addressof(i->second.recent());
            }
            std::invoke(
                std::forward<F>(f), &address, &original_state, current_state);
        }
    }
};

MONAD_NAMESPACE_END
