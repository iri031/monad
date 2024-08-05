#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/rlp/withdrawal_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

// Encode
byte_string encode_transaction_into_block(Transaction const &tx)
{
    if (tx.type == TransactionType::legacy) {
        return encode_transaction(tx);
    }
    else {
        return encode_string2(encode_transaction(tx));
    }
}

byte_string encode_block_header(BlockHeader const &block_header)
{
    byte_string encoded_block_header;
    encoded_block_header += encode_bytes32(block_header.parent_hash);
    encoded_block_header += encode_bytes32(block_header.ommers_hash);
    encoded_block_header += encode_address(block_header.beneficiary);
    encoded_block_header += encode_bytes32(block_header.state_root);
    encoded_block_header += encode_bytes32(block_header.transactions_root);
    encoded_block_header += encode_bytes32(block_header.receipts_root);
    encoded_block_header += encode_bloom(block_header.logs_bloom);
    encoded_block_header += encode_unsigned(block_header.difficulty);
    encoded_block_header += encode_unsigned(block_header.number);
    encoded_block_header += encode_unsigned(block_header.gas_limit);
    encoded_block_header += encode_unsigned(block_header.gas_used);
    encoded_block_header += encode_unsigned(block_header.timestamp);
    encoded_block_header += encode_string2(block_header.extra_data);
    encoded_block_header += encode_bytes32(block_header.prev_randao);
    encoded_block_header +=
        encode_string2(to_byte_string_view(block_header.nonce));

    if (block_header.base_fee_per_gas.has_value()) {
        encoded_block_header +=
            encode_unsigned(block_header.base_fee_per_gas.value());
    }

    if (block_header.withdrawals_root.has_value()) {
        encoded_block_header +=
            encode_bytes32(block_header.withdrawals_root.value());
    }

    return encode_list2(encoded_block_header);
}

byte_string encode_block(Block const &block)
{
    byte_string const encoded_block_header = encode_block_header(block.header);
    byte_string encoded_block_transactions;
    byte_string encoded_block_ommers;

    for (auto const &txn : block.transactions) {
        encoded_block_transactions += encode_transaction_into_block(txn);
    }
    encoded_block_transactions = encode_list2(encoded_block_transactions);

    for (auto const &ommer : block.ommers) {
        encoded_block_ommers += encode_block_header(ommer);
    }
    encoded_block_ommers = encode_list2(encoded_block_ommers);

    byte_string encoded_block;
    encoded_block += encoded_block_header;
    encoded_block += encoded_block_transactions;
    encoded_block += encoded_block_ommers;

    if (block.withdrawals.has_value()) {
        byte_string encoded_block_withdrawals;
        for (auto const &withdraw : block.withdrawals.value()) {
            encoded_block_withdrawals += encode_withdrawal(withdraw);
        }
        encoded_block += encode_list2(encoded_block_withdrawals);
    }

    return encode_list2(encoded_block);
}

// Decode
Result<Transaction> decode_transaction_from_block(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    if (enc[0] < 0xc0) { // EIP-2718
        BOOST_OUTCOME_TRY(auto payload, parse_string_metadata(enc));
        return decode_transaction(payload);
    }
    else {
        return decode_transaction(enc);
    }
}

Result<BlockHeader> decode_block_header(byte_string_view &enc)
{
    BlockHeader block_header;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(block_header.parent_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.ommers_hash, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.beneficiary, decode_address(payload));
    BOOST_OUTCOME_TRY(block_header.state_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.transactions_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.receipts_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.logs_bloom, decode_bloom(payload));
    BOOST_OUTCOME_TRY(
        block_header.difficulty, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(block_header.number, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.gas_limit, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        block_header.timestamp, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(block_header.extra_data, decode_string(payload));
    BOOST_OUTCOME_TRY(block_header.prev_randao, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(block_header.nonce, decode_byte_string_fixed<8>(payload));
    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(
            block_header.base_fee_per_gas, decode_unsigned<uint64_t>(payload));
        if (payload.size() > 0) {
            BOOST_OUTCOME_TRY(
                block_header.withdrawals_root, decode_bytes32(payload));
        }
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return block_header;
}

Result<std::vector<Transaction>>
decode_transaction_vector(byte_string_view &enc)
{
    std::vector<Transaction> txns;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    // TODO: Reserve txn vector size for better perf
    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto txn, decode_transaction_from_block(payload));
        txns.emplace_back(std::move(txn));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return txns;
}

Result<std::vector<BlockHeader>>
decode_block_header_vector(byte_string_view &enc)
{
    std::vector<BlockHeader> ommers;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto ommer, decode_block_header(payload));
        ommers.emplace_back(std::move(ommer));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return ommers;
}

Result<Block> decode_block(byte_string_view &enc)
{
    Block block;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(block.header, decode_block_header(payload));
    BOOST_OUTCOME_TRY(block.transactions, decode_transaction_vector(payload));
    BOOST_OUTCOME_TRY(block.ommers, decode_block_header_vector(payload));

    if (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto withdrawals, decode_withdrawal_list(payload));
        block.withdrawals.emplace(std::move(withdrawals));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return block;
}

MONAD_RLP_NAMESPACE_END
