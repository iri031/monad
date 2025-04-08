#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_access_list(AccessList const &);
byte_string encode_transaction(Transaction const &);
byte_string encode_transaction_for_signing(Transaction const &);

Result<std::vector<bytes32_t>> decode_access_entry_keys(byte_string_view &);
Result<AccessEntry> decode_access_entry(byte_string_view &);
Result<AccessList> decode_access_list(byte_string_view &);

Result<Transaction> decode_transaction_legacy(byte_string_view &);
Result<Transaction> decode_transaction_eip2718(byte_string_view &);
Result<Transaction> decode_transaction(byte_string_view &);
Result<std::vector<Transaction>> decode_transaction_list(byte_string_view &enc);

MONAD_RLP_NAMESPACE_END
