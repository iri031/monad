#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp> // NOLINT
#include <monad/core/fmt/bytes_fmt.hpp> // NOLINT
#include <monad/core/fmt/int_fmt.hpp> // NOLINT
#include <monad/core/keccak.h>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <monad/mpt/node.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rlp/encode2.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

TrieDb::TrieDb(mpt::Db &db)
    : db_{db}
    , block_number_{
          db.get_latest_block_id() == INVALID_BLOCK_ID
              ? 0
              : db.get_latest_block_id()}
{
}

TrieDb::~TrieDb() = default;

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    auto const value = db_.get(
        concat(
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
        block_number_);
    if (!value.has_value()) {
        return std::nullopt;
    }

    auto encoded_account = value.value();
    auto const acct = decode_account_db_ignore_address(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    return acct.value();
}

#define MONAD_TRIEDB_STATS
#ifdef MONAD_TRIEDB_STATS
    #define STATS_STORAGE_NO_VALUE() stats_storage_no_value()
    #define STATS_STORAGE_VALUE() stats_storage_value()
#else
    #define STATS_STORAGE_NO_VALUE()
    #define STATS_STORAGE_VALUE()
#endif

bytes32_t
TrieDb::read_storage(Address const &addr, Incarnation, bytes32_t const &key)
{
    auto const value = db_.get(
        concat(
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
        block_number_);
    if (!value.has_value()) {
        STATS_STORAGE_NO_VALUE();
        return {};
    }
    STATS_STORAGE_VALUE();
    auto encoded_storage = value.value();
    auto const storage = decode_storage_db_ignore_slot(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return to_bytes(storage.value());
};

std::pair<bytes32_t, bytes32_t>
TrieDb::read_storage_and_slot(Address const &addr, bytes32_t const &key)
{
    auto const value = db_.get(
        concat(
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
        block_number_);
    if (!value.has_value()) {
        STATS_STORAGE_NO_VALUE();
        return {};
    }
    STATS_STORAGE_VALUE();
    auto encoded_storage = value.value();
    auto const storage = decode_storage_db(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return storage.value();
};

#ifdef MONAD_TRIEDB_STATS
    #undef STATS_STORAGE_NO_VALUE
    #undef STATS_STORAGE_VALUE
#endif

std::shared_ptr<CodeAnalysis> TrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read code analysis object
    auto const value = db_.get(
        concat(CODE_NIBBLE, NibblesView{to_byte_string_view(code_hash.bytes)}),
        block_number_);
    if (!value.has_value()) {
        return std::make_shared<CodeAnalysis>(analyze({}));
    }
    return std::make_shared<CodeAnalysis>(analyze(value.assume_value()));
}

void TrieDb::commit(
    StateDeltas const &state_deltas, Code const &code,
    std::vector<Receipt> const &receipts)
{
    MONAD_ASSERT(block_number_ <= std::numeric_limits<int64_t>::max());

    UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        UpdateList storage_updates;
        std::optional<byte_string_view> value;
        auto const &account = delta.account.second;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second) {
                    storage_updates.push_front(
                        update_alloc_.emplace_back(Update{
                            .key = hash_alloc_.emplace_back(
                                keccak256({key.bytes, sizeof(key.bytes)})),
                            .value = delta.second == bytes32_t{}
                                         ? std::nullopt
                                         : std::make_optional<byte_string_view>(
                                               bytes_alloc_.emplace_back(
                                                   encode_storage_db(
                                                       key, delta.second))),
                            .incarnation = false,
                            .next = UpdateList{},
                            .version = static_cast<int64_t>(block_number_)}));
                }
            }
            value = bytes_alloc_.emplace_back(
                encode_account_db(addr, account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = hash_alloc_.emplace_back(
                    keccak256({addr.bytes, sizeof(addr.bytes)})),
                .value = value,
                .incarnation = incarnation,
                .next = std::move(storage_updates),
                .version = static_cast<int64_t>(block_number_)}));
        }
    }

    UpdateList code_updates;
    for (auto const &[hash, code_analysis] : code) {
        // TODO write code analysis object
        MONAD_ASSERT(code_analysis);
        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{to_byte_string_view(hash.bytes)},
            .value = code_analysis->executable_code,
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }

    UpdateList receipt_updates;
    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &receipt = receipts[i];
        receipt_updates.push_front(update_alloc_.emplace_back(Update{
            .key =
                NibblesView{bytes_alloc_.emplace_back(rlp::encode_unsigned(i))},
            .value = bytes_alloc_.emplace_back(rlp::encode_receipt(receipt)),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }
    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto receipt_update = Update{
        .key = receipt_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(receipt_updates),
        .version = static_cast<int64_t>(block_number_)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(receipt_update);
    db_.upsert(std::move(updates), block_number_);

    update_alloc_.clear();
    bytes_alloc_.clear();
    hash_alloc_.clear();
}

void TrieDb::increment_block_number()
{
    if (db_.is_on_disk()) {
        ++block_number_;
    }
}

bytes32_t TrieDb::state_root()
{
    return merkle_root(state_nibbles);
}

bytes32_t TrieDb::receipts_root()
{
    return merkle_root(receipt_nibbles);
}

bytes32_t TrieDb::merkle_root(mpt::Nibbles const &nibbles)
{
    auto const value = db_.get_data(nibbles, block_number_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

std::string TrieDb::print_stats()
{
    std::string ret;
    ret += std::format(
        "{:6} {:6}",
        n_storage_no_value_.load(std::memory_order_acquire),
        n_storage_value_.load(std::memory_order_acquire));
    n_storage_no_value_.store(0, std::memory_order_release);
    n_storage_value_.store(0, std::memory_order_release);
    return ret;
}

nlohmann::json TrieDb::to_json()
{
    struct Traverse : public TraverseMachine
    {
        TrieDb &db;
        nlohmann::json &json;
        Nibbles path{};

        explicit Traverse(TrieDb &db, nlohmann::json &json)
            : db(db)
            , json(json)
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
                return true;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (path.nibble_size() == (KECCAK256_SIZE * 2)) {
                handle_account(node);
            }
            else if (
                path.nibble_size() == ((KECCAK256_SIZE + KECCAK256_SIZE) * 2)) {
                handle_storage(node);
            }
            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            auto const path_view = NibblesView{path};
            auto const rem_size = [&] {
                if (branch == INVALID_BRANCH) {
                    MONAD_ASSERT(path_view.nibble_size() == 0);
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_ASSERT(rem_size >= 0);
                MONAD_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        void handle_account(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto encoded_account = node.value();

            auto acct = decode_account_db(encoded_account);
            MONAD_DEBUG_ASSERT(!acct.has_error());

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["address"] = fmt::format("{}", acct.value().first);
            json[key]["balance"] =
                fmt::format("{}", acct.value().second.balance);
            json[key]["nonce"] =
                fmt::format("0x{:x}", acct.value().second.nonce);

            auto const code_analysis =
                db.read_code(acct.value().second.code_hash);
            MONAD_ASSERT(code_analysis);
            json[key]["code"] =
                "0x" + evmc::hex(code_analysis->executable_code);

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto encoded_storage = node.value();

            auto const storage = decode_storage_db(encoded_storage);
            MONAD_DEBUG_ASSERT(!storage.has_error());

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            auto const key = fmt::format(
                "{}",
                NibblesView{path}.substr(
                    KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

            auto storage_data_json = nlohmann::json::object();
            storage_data_json["slot"] = fmt::format(
                "0x{:02x}",
                fmt::join(
                    std::as_bytes(std::span(storage.value().first.bytes)), ""));
            storage_data_json["value"] = fmt::format(
                "0x{:02x}",
                fmt::join(
                    std::as_bytes(std::span(storage.value().second.bytes)),
                    ""));
            json[acct_key]["storage"][key] = storage_data_json;
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }
    };

    auto json = nlohmann::json::object();
    Traverse traverse(*this, json);

    auto res_cursor = db_.find(state_nibbles, block_number_);
    MONAD_ASSERT(res_cursor.has_value());
    MONAD_ASSERT(res_cursor.value().is_valid());
    // RWOndisk Db prevents any parallel traversal that does blocking i/o
    // from running on the triedb thread, which include to_json. Thus, we can
    // only use blocking traversal for RWOnDisk Db, but can still do parallel
    // traverse in other cases.
    if (db_.is_on_disk() && !db_.is_read_only()) {
        MONAD_ASSERT(
            db_.traverse_blocking(res_cursor.value(), traverse, block_number_));
    }
    else {
        // WARNING: excessive memory usage in parallel traverse
        MONAD_ASSERT(db_.traverse(res_cursor.value(), traverse, block_number_));
    }

    return json;
}

size_t TrieDb::prefetch_current_root()
{
    return db_.prefetch();
}

uint64_t TrieDb::get_block_number() const
{
    return block_number_;
}

void TrieDb::set_block_number(uint64_t const n)
{
    block_number_ = n;
}

MONAD_NAMESPACE_END
