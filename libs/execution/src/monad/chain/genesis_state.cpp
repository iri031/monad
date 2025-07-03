#include <monad/chain/genesis_state.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/execution/trace/prestate_tracer.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

void load_genesis_state(GenesisState const &genesis, TrieDb &db)
{
    MONAD_ASSERT(genesis.alloc);
    MONAD_ASSERT(
        genesis.header.withdrawals_root == NULL_ROOT ||
        !genesis.header.withdrawals_root.has_value());
    StateDeltas deltas;
    auto const json = nlohmann::json::parse(genesis.alloc);
    for (auto const &item : json.items()) {
        Address const addr = evmc::from_hex<Address>(item.key()).value();
        Account account{};
        account.balance =
            intx::from_string<uint256_t>(item.value()["wei_balance"]);
        deltas.emplace(addr, StateDelta{.account = {std::nullopt, account}});
    }
    MonadConsensusBlockHeader header;
    header.execution_inputs = genesis.header;
    db.commit(
        deltas,
        Code{},
        header,
        std::vector<Receipt>{},
        std::vector<std::vector<CallFrame>>{},
        std::vector<PreState>{},
        std::vector<StateDeltas>{},
        std::vector<Address>{},
        std::vector<Transaction>{},
        std::vector<BlockHeader>{},
        genesis.header.withdrawals_root == NULL_ROOT
            ? std::make_optional<std::vector<Withdrawal>>()
            : std::nullopt);
    db.finalize(0, 0);
}

MONAD_NAMESPACE_END
