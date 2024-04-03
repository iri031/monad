#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>
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
Result<evmc::Result> eth_call(
    Transaction const &txn, BlockHeader const &header, uint64_t const block_id,
    Address const sender, BlockHashBuffer const &buffer,
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
