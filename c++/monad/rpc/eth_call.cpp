#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/rpc/eth_call.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/try.hpp>

MONAD_RPC_NAMESPACE_BEGIN

/*
    For eth_call with real txn, submit as it is
    For eth_call with only "from" "to" and "data", set txn.value = 0 & gas_limit
    to a big number to guarantee success on txn side if no "from", set from =
    "0x0000...00"
*/

evmc_result eth_call(
    std::vector<uint8_t> const &rlp_encoded_transaction,
    std::vector<uint8_t> const &rlp_encoded_block_header,
    std::vector<uint8_t> const &rlp_encoded_sender, uint64_t const block_id,
    std::string const &trie_db_path, std::string const &block_db_path)
{
    byte_string_view encoded_transaction(
        rlp_encoded_transaction.begin(), rlp_encoded_transaction.end());
    byte_string_view encoded_block_header(
        rlp_encoded_block_header.begin(), rlp_encoded_block_header.end());
    byte_string_view encoded_sender(
        rlp_encoded_sender.begin(), rlp_encoded_sender.end());

    auto const txn_result = rlp::decode_transaction(encoded_transaction);
    MONAD_ASSERT(!txn_result.has_error());
    auto const txn = txn_result.value();

    auto const block_header_result =
        rlp::decode_block_header(encoded_block_header);
    MONAD_ASSERT(!block_header_result.has_error());
    auto const block_header = block_header_result.value();

    auto const sender_result = rlp::decode_address(encoded_sender);
    MONAD_ASSERT(!sender_result.has_error());
    auto const sender = sender_result.value();

    BlockHashBuffer buffer{};
    uint64_t start_block_number = block_id < 256 ? 1 : block_id - 255;
    BlockDb block_db{block_db_path.c_str()};

    while (start_block_number < block_id) {
        Block block{};
        bool const result = block_db.get(start_block_number, block);
        MONAD_ASSERT(result);
        buffer.set(start_block_number - 1, block.header.parent_hash);
        ++start_block_number;
    }

    // TODO: construct trie_db_path properly
    auto result = eth_call_helper(
        txn, block_header, block_id, sender, buffer, {trie_db_path.c_str()});
    if (MONAD_UNLIKELY(result.has_error())) {
        // TODO: If validation fails, just return as generic failure for now
        evmc_result res{};
        res.status_code = EVMC_FAILURE;
        return res;
    }

    return result.value().release_raw();
}

Result<evmc::Result> eth_call_helper(
    Transaction const &txn, BlockHeader const &header, uint64_t const block_id,
    Address const &sender, BlockHashBuffer const &buffer,
    std::vector<std::filesystem::path> const &dbname_paths)
{
    // TODO: Hardset rev to be Shanghai at the moment
    static constexpr auto rev = EVMC_SHANGHAI;
    Transaction enriched_txn{txn};

    // SignatureAndChain validation hacks
    enriched_txn.sc.chain_id = 1;
    enriched_txn.sc.r = 1;
    enriched_txn.sc.s = 1;

    BOOST_OUTCOME_TRY(
        static_validate_transaction<rev>(enriched_txn, header.base_fee_per_gas))

    mpt::ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = dbname_paths};
    TrieDbRO trie_db_ro{ro_config, block_id};
    BlockState block_state{trie_db_ro};
    State state{block_state};

    auto const sender_account = state.recent_account(sender);

    // nonce validation hack
    enriched_txn.nonce =
        sender_account.has_value() ? sender_account.value().nonce : 0;

    BOOST_OUTCOME_TRY(validate_transaction(enriched_txn, sender_account));

    auto const tx_context = get_tx_context<rev>(enriched_txn, sender, header);
    EvmcHost<rev> host{tx_context, buffer, state};

    return execute_impl_no_validation<rev>(
        state,
        host,
        enriched_txn,
        sender,
        header.base_fee_per_gas.value_or(0),
        header.beneficiary);
}

MONAD_RPC_NAMESPACE_END
