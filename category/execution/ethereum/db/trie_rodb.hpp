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

#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt2/db.hpp>
#include <category/vm/vm.hpp>

#include <evmc/hex.hpp>

#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

class TrieRODb final : public ::monad::Db
{
    ::monad::mpt2::RODb &db_;
    uint64_t block_number_;
    ::monad::mpt2::OwningNodeCursor prefix_cursor_;

public:
    TrieRODb(mpt2::RODb &db)
        : db_(db)
        , block_number_(mpt2::INVALID_BLOCK_NUM)
        , prefix_cursor_()
    {
    }

    ~TrieRODb() = default;

    virtual void set_block_and_prefix(
        uint64_t const block_number,
        bytes32_t const &block_id = bytes32_t{}) override
    {
        auto const prefix = block_id == bytes32_t{} ? finalized_nibbles
                                                    : proposal_prefix(block_id);
        auto res = db_.find(prefix, block_number);
        // TODO: error handling instead of assert
        MONAD_ASSERT_PRINTF(
            res.has_value(),
            "block %lu, block_id %s",
            block_number,
            evmc::hex(to_byte_string_view(block_id.bytes)).c_str());
        prefix_cursor_ = std::move(res.value());
        block_number_ = block_number;
    }

    virtual std::optional<Account> read_account(Address const &addr) override
    {
        auto acc_leaf_res = db_.find(
            prefix_cursor_.clone(),
            mpt2::concat(
                STATE_NIBBLE,
                mpt2::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
            block_number_);
        if (!acc_leaf_res.has_value()) {
            return std::nullopt;
        }
        auto encoded_account = acc_leaf_res.value().node->value();
        auto const acct = decode_account_db_ignore_address(encoded_account);
        MONAD_DEBUG_ASSERT(!acct.has_error());
        return acct.value();
    }

    virtual bytes32_t read_storage(
        Address const &addr, Incarnation, bytes32_t const &key) override
    {
        auto storage_leaf_res = db_.find(
            prefix_cursor_.clone(),
            mpt2::concat(
                STATE_NIBBLE,
                mpt2::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                mpt2::NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
            block_number_);
        if (!storage_leaf_res.has_value()) {
            return {};
        }
        auto encoded_storage = storage_leaf_res.value().node->value();
        auto const storage = decode_storage_db_ignore_slot(encoded_storage);
        MONAD_ASSERT(!storage.has_error());
        return to_bytes(storage.value());
    }

    virtual vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        // TODO read intercode object
        auto code_leaf_res = db_.find(
            prefix_cursor_.clone(),
            mpt2::concat(
                CODE_NIBBLE,
                mpt2::NibblesView{to_byte_string_view(code_hash.bytes)}),
            block_number_);
        if (!code_leaf_res.has_value()) {
            return vm::make_shared_intercode({});
        }
        return vm::make_shared_intercode(code_leaf_res.value().node->value());
    }

    virtual void commit(
        StateDeltas const &, Code const &, bytes32_t const &,
        BlockHeader const &, std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const & = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt) override
    {
        MONAD_ABORT();
    }

    virtual void finalize(uint64_t, bytes32_t const &) override
    {
        MONAD_ABORT();
    }

    virtual void update_verified_block(uint64_t) override
    {
        MONAD_ABORT();
    }

    virtual void update_voted_metadata(uint64_t, bytes32_t const &) override
    {
        MONAD_ABORT();
    }

    virtual BlockHeader read_eth_header() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t state_root() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t receipts_root() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t transactions_root() override
    {
        MONAD_ABORT();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        MONAD_ABORT();
    }
};

MONAD_NAMESPACE_END
