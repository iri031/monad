#include <monad/async/util.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.h>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <fuzzer/FuzzedDataProvider.h>
#include <intx/intx.hpp>
#include <quill/Quill.h>
#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <algorithm>
#include <iterator>
#include <list>
#include <memory>
#include <optional>
#include <set>

using namespace monad;

static auto ctx = []() {
    std::unique_ptr<secp256k1_context, decltype(&secp256k1_context_destroy)>
        context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            secp256k1_context_destroy);
    return context;
}();

std::filesystem::path tmp_dbname()
{
    std::filesystem::path dbname(
        MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
        "monad_fuzz_execution_XXXXXX");
    int const fd = ::mkstemp((char *)dbname.native().data());
    MONAD_ASSERT(fd != -1);
    MONAD_ASSERT(
        -1 != ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
    ::close(fd);
    char const *const path = dbname.c_str();
    OnDiskMachine machine;
    mpt::Db const db{
        machine, mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
    return dbname;
}

class Wallet
{
public:
    bytes32_t privkey_;
    secp256k1_pubkey pubkey_;
    Address address_;

public:
    Wallet(bytes32_t const &privkey)
        : privkey_{privkey}
    {
        secp256k1_pubkey pubkey{};
        if (!secp256k1_ec_pubkey_create(ctx.get(), &pubkey, privkey_.bytes)) {
            MONAD_ABORT("Could not generate wallet");
        }

        unsigned char serialized_pubkey[65];
        size_t pubkey_len = sizeof(serialized_pubkey);
        if (!secp256k1_ec_pubkey_serialize(
                ctx.get(),
                serialized_pubkey,
                &pubkey_len,
                &pubkey,
                SECP256K1_EC_UNCOMPRESSED)) {
            MONAD_ABORT("Could not serialize pubkey");
        }
        MONAD_ASSERT(serialized_pubkey[0] == 4);
        auto const hash =
            keccak256(byte_string_view{serialized_pubkey + 1, 64});
        std::copy_n(hash.bytes + 12, sizeof(Address), address_.bytes);
    }

    Address const &address() const
    {
        return address_;
    }

    void sign(
        bytes32_t const &msg_hash, uint256_t &r, uint256_t &s,
        bool &odd_y_parity) const
    {
        secp256k1_ecdsa_recoverable_signature sig{};
        if (!secp256k1_ecdsa_sign_recoverable(
                ctx.get(),
                &sig,
                msg_hash.bytes,
                privkey_.bytes,
                nullptr,
                nullptr)) {
            MONAD_ABORT("Could not sign mesasge");
        }

        unsigned char compact_sig[64];
        int recid{};
        if (!secp256k1_ecdsa_recoverable_signature_serialize_compact(
                ctx.get(), compact_sig, &recid, &sig)) {
            MONAD_ABORT("Could not get signature parity");
        }

        unsigned char r2[32];
        unsigned char s2[32];
        std::copy_n(compact_sig, 32, r2);
        std::copy_n(compact_sig + 32, 32, s2);
        r = intx::be::load<uint256_t>(r2);
        s = intx::be::load<uint256_t>(s2);
        odd_y_parity = static_cast<bool>(recid);
    }
};

class BlockFuzzer
{
    TrieDb &tdb_;
    FuzzedDataProvider &provider_;
    struct Proposal;

    struct Proposal
    {
        std::list<Proposal>::iterator parent;
        BlockHeader header;
    };

    BlockHashBufferFinalized block_hash_buffer_;
    BlockHashChain block_hash_chain_;
    std::vector<Wallet> wallets_;
    std::list<Proposal> proposals_;
    std::unique_ptr<Chain> chain_;
    BlockHeader last_finalized_;
    uint64_t proposed_round_lower_bound_;
    fiber::PriorityPool priority_pool_;

    Block generate_proposal(
        BlockHeader const &parent, uint64_t const round_lower_bound)
    {
        Block block;

        auto &header = block.header;

        header.round = round_lower_bound +
                       provider_.ConsumeIntegralInRange<uint64_t>(0, 100);
        header.parent_round = parent.round;
        header.number = parent.number + 1;

        header.difficulty = uint256_t{0};
        header.gas_limit = 60'000;
        provider_.ConsumeData(
            header.bft_block_id.bytes, sizeof(header.bft_block_id));
        header.beneficiary =
            wallets_[provider_.ConsumeIntegralInRange<uint64_t>(
                         0, wallets_.size() - 1)]
                .address();
        header.timestamp = parent.timestamp +
                           provider_.ConsumeIntegralInRange<uint64_t>(1, 1000);
        header.base_fee_per_gas = 1;
        provider_.ConsumeData(
            header.prev_randao.bytes, sizeof(header.prev_randao));

        block.withdrawals.emplace(std::vector<Withdrawal>{});

        tdb_.set(header.number, header.round, header.parent_round);

        auto const num_txns = provider_.ConsumeIntegralInRange<uint64_t>(0, 5);
        std::unordered_map<Address, uint64_t> nonces{};
        for (uint64_t i = 0; i < num_txns; ++i) {
            auto const fi = provider_.ConsumeIntegralInRange<uint64_t>(
                0, wallets_.size() - 1);
            auto const ti = provider_.ConsumeIntegralInRange<uint64_t>(
                0, wallets_.size() - 1);
            auto const &from = wallets_[fi];
            auto const &to = wallets_[ti];

            auto account = tdb_.read_account(from.address());
            MONAD_ASSERT(account.has_value());
            auto [it, _] = nonces.try_emplace(from.address(), account->nonce);
            Transaction tx{
                .sc = SignatureAndChain{.chain_id = chain_->get_chain_id()},
                .nonce = it->second,
                .max_fee_per_gas = 1,
                .gas_limit = 60'000,
                .value = 10,
                .to = to.address(),
                .type = TransactionType::legacy,
                .data = byte_string{}};
            ++it->second;

            uint512_t const v0 =
                tx.value + max_gas_cost(tx.gas_limit, tx.max_fee_per_gas);
            if (account->balance < v0) {
                MONAD_ABORT("fuzzer logic error");
            }

            auto const hash =
                keccak256(rlp::encode_transaction_for_signing(tx));
            from.sign(
                std::bit_cast<bytes32_t>(hash),
                tx.sc.r,
                tx.sc.s,
                tx.sc.odd_y_parity);
            block.transactions.emplace_back(std::move(tx));
        }
        return block;
    }

    void finalize_proposal(std::list<Proposal>::iterator it)
    {
        if (it->parent != proposals_.end()) {
            finalize_proposal(it->parent);
        }
        block_hash_chain_.finalize(it->header.round);
        last_finalized_ = std::move(it->header);
        proposals_.erase(it);
    }

    void execute_or_fail(Block &block)
    {
        if (auto const res = chain_->static_validate_header(block.header);
            res.has_error()) {
            MONAD_ABORT(
                "Error validating header(%lu, %lu): %s",
                block.header.number,
                block.header.round,
                res.error().message().c_str());
        }

        evmc_revision const rev = chain_->get_revision(block.header.number);

        if (auto const res = static_validate_block(rev, block);
            res.has_error()) {
            MONAD_ABORT(
                "Error validating block(%lu, %lu): %s",
                block.header.number,
                block.header.round,
                res.error().message().c_str());
        }

        tdb_.set(
            block.header.number, block.header.round, block.header.parent_round);

        auto const &block_hash_buffer =
            block_hash_chain_.find_chain(block.header.parent_round);
        BlockState block_state{tdb_};

        auto const results = execute_block(
            *chain_,
            rev,
            block,
            block_state,
            block_hash_buffer,
            priority_pool_);
        if (results.has_error()) {
            MONAD_ABORT(
                "Failed executing block(%lu, %lu): %s",
                block.header.number,
                block.header.round,
                results.error().message().c_str());
        }
        std::vector<Receipt> receipts(results.value().size());

        std::vector<std::vector<CallFrame>> call_frames(results.value().size());
        for (unsigned i = 0; i < results.value().size(); ++i) {
            auto &result = results.value()[i];
            receipts[i] = std::move(result.receipt);
            call_frames[i] = (std::move(result.call_frames));
        }

        block_state.commit(
            block.header,
            receipts,
            block.header.bft_block_id,
            call_frames,
            block.transactions,
            block.ommers,
            block.withdrawals);
    }

public:
    BlockFuzzer(TrieDb &tdb, FuzzedDataProvider &provider)
        : tdb_{tdb}
        , provider_{provider}
        , block_hash_chain_{block_hash_buffer_}
        , priority_pool_{1, 1}
    {

        BlockState bs{tdb_};
        State state{bs, Incarnation{0, 0}};
        std::set<bytes32_t> used_keys{};
        while (wallets_.size() < 10) {
            bytes32_t key;
            provider_.ConsumeData(key.bytes, sizeof(bytes32_t));
            if (!used_keys.contains(key)) {
                used_keys.insert(key);
                auto const &w = wallets_.emplace_back(key);
                state.add_to_balance(w.address(), 1'000'000'000'000);
            }
        }
        bs.merge(state);
        tdb_.set(0, 0, 0); // genesis
        bs.commit({}, {}, {}, {}, {}, {}, std::nullopt);
        auto genesis_header = tdb_.read_header();
        MONAD_ASSERT(genesis_header.has_value());
        tdb_.finalize(0, 0);
        block_hash_buffer_.set(
            0,
            std::bit_cast<bytes32_t>(
                keccak256(rlp::encode_block_header(genesis_header.value()))));

        proposed_round_lower_bound_ = 1;

        chain_ = std::make_unique<MonadDevnet>();
    }

    void next()
    {
        if (provider_.ConsumeBool()) {
            if (provider_.ConsumeProbability<float>() <= 0.2f) {
                Block next_block = generate_proposal(
                    last_finalized_, proposed_round_lower_bound_);
                proposals_.push_back(Proposal{
                    .parent = proposals_.end(), .header = next_block.header});
                proposed_round_lower_bound_ =
                    proposals_.back().header.round + 1;
                execute_or_fail(next_block);
            }
            else if (!proposals_.empty() && provider_.ConsumeBool()) {
                size_t parent_idx = provider_.ConsumeIntegralInRange<size_t>(
                    0, proposals_.size() - 1);
                auto it = proposals_.begin();
                std::advance(it, parent_idx);
                Block next_block =
                    generate_proposal(it->header, proposed_round_lower_bound_);
                proposals_.push_back(
                    Proposal{.parent = it, .header = next_block.header});
                proposed_round_lower_bound_ =
                    proposals_.back().header.round + 1;
                execute_or_fail(next_block);
            }
        }
        else if (!proposals_.empty()) {
            size_t finalize_idx = provider_.ConsumeIntegralInRange<size_t>(
                0, proposals_.size() - 1);
            auto it = proposals_.begin();
            std::advance(it, finalize_idx);
            finalize_proposal(std::move(it));

            // GC old proposals
            for (auto it = proposals_.begin(); it != proposals_.end(); ++it) {
                if (it->header.parent_round <= last_finalized_.round) {
                    it->parent = proposals_.end();
                }
            }
            for (auto it = proposals_.begin(); it != proposals_.end();) {
                if (it->header.round <= last_finalized_.round) {
                    it = proposals_.erase(it);
                }
                else {
                    ++it;
                }
            }
        }
    }
};

struct __attribute__((packed)) FuzzParams
{
    uint64_t num_accounts;
    uint16_t num_events;
    uint32_t seed;
};

extern "C" int LLVMFuzzerTestOneInput(uint8_t const *data, size_t size)
{
    if (size < sizeof(FuzzParams)) {
        return -1;
    }

    auto const params = unaligned_load<FuzzParams>(data);
    std::vector<uint32_t> data_source;
    data_source.resize(1ULL * 1024 * 1024 * 1024 / sizeof(uint32_t));
    small_prng rng{params.seed};
    std::generate(data_source.begin(), data_source.end(), rng);

    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Error);

    auto dbname = tmp_dbname();
    OnDiskMachine machine;
    mpt::Db db{
        machine, mpt::OnDiskDbConfig{.append = true, .dbname_paths = {dbname}}};
    TrieDb tdb{db};

    FuzzedDataProvider provider(
        reinterpret_cast<uint8_t const *>(data_source.data()),
        data_source.size() * sizeof(uint32_t));
    BlockFuzzer fuzzer(tdb, provider);

    for (uint16_t e = 0; e < params.num_events; ++e) {
        fuzzer.next();
    }

    return 0;
}
