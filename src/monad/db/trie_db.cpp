#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/int_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/config.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rlp/encode2.hpp>

#include <evmone/baseline.hpp>

#include <evmc/evmc.hpp>

#include <ethash/keccak.hpp>

#include <boost/json.hpp>
#include <boost/json/basic_parser_impl.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <deque>
#include <set>

MONAD_DB_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    constexpr unsigned char state_nibble = 0;
    constexpr unsigned char code_nibble = 1;
    constexpr unsigned char receipt_nibble = 2;
    auto const state_nibbles = concat(state_nibble);
    auto const code_nibbles = concat(code_nibble);
    auto const receipt_nibbles = concat(receipt_nibble);

    template <class T>
        requires std::same_as<T, bytes32_t> || std::same_as<T, Address>
    constexpr byte_string to_key(T const &arg)
    {
        return byte_string{
            std::bit_cast<bytes32_t>(
                ethash::keccak256(arg.bytes, sizeof(arg.bytes)))
                .bytes,
            sizeof(bytes32_t)};
    }

    struct LeafCompute
    {
        static byte_string compute(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            // this is the block number leaf
            if (MONAD_UNLIKELY(node.value().empty())) {
                return {};
            }
            // this is a storage leaf
            else if (
                node.value().size() <= sizeof(bytes32_t) &&
                node.value()[0] != 0x00) {
                MONAD_ASSERT(node.value().front());
                return rlp::encode_string2(node.value());
            }

            auto encoded_account = node.value();
            auto const acct = rlp::decode_account(encoded_account);
            MONAD_DEBUG_ASSERT(!acct.has_error());
            MONAD_DEBUG_ASSERT(encoded_account.empty());
            bytes32_t storage_root = NULL_ROOT;
            if (node.number_of_children()) {
                MONAD_ASSERT(node.data().size() == sizeof(bytes32_t));
                std::copy_n(
                    node.data().data(), sizeof(bytes32_t), storage_root.bytes);
            }
            return rlp::encode_account(acct.value(), storage_root);
        }
    };

    using MerkleCompute = MerkleComputeBase<LeafCompute>;

    struct RootMerkleCompute final : public MerkleCompute
    {
        virtual unsigned compute(unsigned char *const, Node *const) override
        {
            return 0;
        }
    };

    struct EmptyCompute final : Compute
    {
        virtual unsigned compute_len(
            std::span<ChildData>, uint16_t, NibblesView,
            std::optional<byte_string_view>) override
        {
            return 0;
        }

        virtual unsigned compute_branch(unsigned char *, Node *) override
        {
            return 0;
        }

        virtual unsigned compute(unsigned char *, Node *) override
        {
            return 0;
        }
    };

    struct JsonDbLoader
    {
        static constexpr size_t max_object_size = std::size_t(-1);
        static constexpr size_t max_array_size = std::size_t(-1);
        static constexpr size_t max_key_size = std::size_t(-1);
        static constexpr size_t max_string_size = std::size_t(-1);
        static constexpr size_t bytes32_size = sizeof(bytes32_t) * 2 + 2;

        enum class State
        {
            Root = 0,
            Accounts,
            Account,
            Balance,
            Code,
            Nonce,
            Storage
        } state_;

        std::string key_;
        std::string value_;
        byte_string acct_key_;
        Account acct_;
        std::deque<mpt::Update> update_alloc_;
        std::deque<byte_string> bytes_alloc_;
        UpdateList account_updates_;
        UpdateList code_updates_;
        ::monad::mpt::Db &db_;
        size_t batch_size_;
        UpdateList storage_updates_;
        std::set<bytes32_t> inserted_code_;
        uint64_t block_id_;

        JsonDbLoader(
            ::monad::mpt::Db &db, size_t batch_size, uint64_t const block_id)
            : state_{State::Root}
            , db_{db}
            , batch_size_{batch_size}
            , block_id_{block_id}
        {
        }

        bool on_document_begin(std::error_code &)
        {
            MONAD_ASSERT(state_ == State::Root);
            return true;
        }

        bool on_document_end(std::error_code &)
        {
            MONAD_ASSERT(state_ == State::Root);
            return true;
        }

        bool on_object_begin(std::error_code &)
        {
            if (state_ == State::Root) {
                state_ = State::Accounts;
            }
            else if (state_ == State::Accounts) {
                state_ = State::Account;
            }
            else if (state_ == State::Account) {
                state_ = State::Storage;
            }
            else {
                MONAD_ASSERT(false);
            }
            return true;
        }

        bool on_object_end(size_t, std::error_code &)
        {
            if (state_ == State::Accounts) {
                state_ = State::Root;
            }
            else if (state_ == State::Account) {
                account_updates_.push_front(update_alloc_.emplace_back(Update{
                    .key = bytes_alloc_.emplace_back(acct_key_),
                    .value =
                        bytes_alloc_.emplace_back(rlp::encode_account(acct_)),
                    .incarnation = false,
                    .next = std::move(storage_updates_)}));
                storage_updates_.clear();

                if (account_updates_.size() >= batch_size_) {
                    static_assert(UpdateList::constant_time_size);
                    write();
                }
                state_ = State::Accounts;
            }
            else if (state_ == State::Storage) {
                state_ = State::Account;
            }
            else {
                MONAD_ASSERT(false);
            }
            return true;
        }

        bool on_array_begin(std::error_code &)
        {
            return false;
        }

        bool on_array_end(size_t, std::error_code &)
        {
            return false;
        }

        bool on_key_part(std::string_view in, size_t n, std::error_code &)
        {
            append_to(key_, in, n);
            return true;
        }

        bool on_key(std::string_view in, size_t n, std::error_code &)
        {
            append_to(key_, in, n);

            if (state_ == State::Accounts) {
                MONAD_ASSERT(n == bytes32_size);
                acct_key_ = evmc::from_hex(key_).value();
                key_.clear();
            }
            else if (state_ == State::Account) {
                if (key_ == "balance") {
                    state_ = State::Balance;
                }
                else if (key_ == "nonce") {
                    state_ = State::Nonce;
                }
                else if (key_ == "code") {
                    state_ = State::Code;
                }
                else if (key_ != "storage") {
                    MONAD_ASSERT(false);
                }
                key_.clear();
            }
            else if (state_ == State::Storage) {
                MONAD_ASSERT(n == bytes32_size);
            }
            else {
                MONAD_ASSERT(false);
            }

            return true;
        }

        bool on_string_part(std::string_view in, size_t n, std::error_code &)
        {
            append_to(value_, in, n);
            return true;
        }

        bool on_string(std::string_view in, size_t n, std::error_code &)
        {
            append_to(value_, in, n);
            if (state_ == State::Balance) {
                state_ = State::Account;
                acct_.balance = intx::from_string<uint256_t>(value_);
            }
            else if (state_ == State::Code) {
                state_ = State::Account;
                auto const &code =
                    bytes_alloc_.emplace_back(evmc::from_hex(value_).value());
                acct_.code_hash = std::bit_cast<bytes32_t>(
                    ethash::keccak256(code.data(), code.size()));
                if (!inserted_code_.contains(acct_.code_hash)) {
                    if (acct_.code_hash != NULL_HASH) {
                        code_updates_.push_front(
                            update_alloc_.emplace_back(Update{
                                .key = bytes_alloc_.emplace_back(
                                    to_byte_string_view(acct_.code_hash.bytes)),
                                .value = code,
                                .incarnation = false,
                                .next = UpdateList{}}));
                    }
                    inserted_code_.insert(acct_.code_hash);
                }
            }
            else if (state_ == State::Nonce) {
                state_ = State::Account;
                acct_.nonce = std::stoull(value_, nullptr, 16);
            }
            else if (state_ == State::Storage) {
                MONAD_ASSERT(value_.size() == bytes32_size);
                storage_updates_.push_front(update_alloc_.emplace_back(Update{
                    .key =
                        bytes_alloc_.emplace_back(evmc::from_hex(key_).value()),
                    .value = bytes_alloc_.emplace_back(
                        rlp::zeroless_view(evmc::from_hex(value_).value())),
                    .incarnation = false,
                    .next = UpdateList{}}));
                key_.clear();
            }
            else {
                MONAD_ASSERT(false);
            }

            value_.clear();
            return true;
        }

        bool on_number_part(std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_int64(std::int64_t, std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_uint64(std::uint64_t, std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_double(double, std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_bool(bool, std::error_code &)
        {
            return false;
        }

        bool on_null(std::error_code &)
        {
            return false;
        }

        bool on_comment_part(std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_comment(std::string_view, std::error_code &)
        {
            return false;
        }

        void append_to(std::string &to, std::string_view in, size_t n)
        {
            to.append(in);
            MONAD_ASSERT(to.size() == n);
        }

        void write()
        {
            UpdateList updates;
            updates.push_front(update_alloc_.emplace_back(Update{
                .key = state_nibbles,
                .value = byte_string_view{},
                .incarnation = false,
                .next = std::move(account_updates_)}));
            updates.push_front(update_alloc_.emplace_back(Update{
                .key = code_nibbles,
                .value = byte_string_view{},
                .incarnation = false,
                .next = std::move(code_updates_)}));

            db_.upsert(std::move(updates), block_id_, false);

            inserted_code_.clear();
            account_updates_.clear();
            code_updates_.clear();
            update_alloc_.clear();
            bytes_alloc_.clear();
        }
    };

    struct BinaryDbLoader
    {
    private:
        static constexpr auto chunk_size = 1ul << 13; // 8 kb

        ::monad::mpt::Db &db_;
        std::deque<mpt::Update> update_alloc_;
        std::deque<byte_string> bytes_alloc_;
        size_t buf_size_;
        std::unique_ptr<unsigned char[]> buf_;
        uint64_t block_id_;

    public:
        BinaryDbLoader(
            ::monad::mpt::Db &db, size_t buf_size, uint64_t const block_id)
            : db_{db}
            , buf_size_{buf_size}
            , buf_{std::make_unique_for_overwrite<unsigned char[]>(buf_size)}
            , block_id_{block_id}
        {
            MONAD_ASSERT(buf_size >= chunk_size);
        };

        void load(std::istream &accounts, std::istream &code)
        {
            load(
                accounts,
                [&](byte_string_view in, UpdateList &updates) {
                    return parse_accounts(in, updates);
                },
                [&](UpdateList account_updates) {
                    UpdateList updates;
                    auto state_update = Update{
                        .key = state_nibbles,
                        .value = byte_string_view{},
                        .incarnation = false,
                        .next = std::move(account_updates)};
                    updates.push_front(state_update);

                    db_.upsert(std::move(updates), block_id_, false);

                    update_alloc_.clear();
                    bytes_alloc_.clear();
                });
            load(
                code,
                [&](byte_string_view in, UpdateList &updates) {
                    return parse_code(in, updates);
                },
                [&](UpdateList code_updates) {
                    UpdateList updates;
                    auto code_update = Update{
                        .key = code_nibbles,
                        .value = byte_string_view{},
                        .incarnation = false,
                        .next = std::move(code_updates)};
                    updates.push_front(code_update);

                    db_.upsert(std::move(updates), block_id_, false);

                    update_alloc_.clear();
                    bytes_alloc_.clear();
                });
        }

    private:
        static constexpr auto storage_entry_size = sizeof(bytes32_t) * 2;
        static_assert(storage_entry_size == 64);

        void load(
            std::istream &input,
            std::function<size_t(byte_string_view, UpdateList &)> fparse,
            std::function<void(UpdateList)> fwrite)
        {
            UpdateList updates;
            size_t total_processed = 0;
            size_t total_read = 0;
            while (input.read((char *)buf_.get() + total_read, chunk_size)) {
                auto const count = static_cast<size_t>(input.gcount());
                MONAD_ASSERT(count <= chunk_size);
                total_read += count;
                total_processed += fparse(
                    byte_string_view{
                        buf_.get() + total_processed,
                        total_read - total_processed},
                    updates);
                if (MONAD_UNLIKELY((total_read + chunk_size) > buf_size_)) {
                    fwrite(std::move(updates));
                    std::memmove(
                        buf_.get(),
                        buf_.get() + total_processed,
                        total_read - total_processed);
                    total_read -= total_processed;
                    total_processed = 0;
                    updates.clear();
                }
            }

            auto const count = static_cast<size_t>(input.gcount());
            MONAD_ASSERT(count <= chunk_size);
            total_read += count;
            total_processed += fparse(
                byte_string_view{
                    buf_.get() + total_processed, total_read - total_processed},
                updates);
            MONAD_ASSERT(total_processed == total_read);
            MONAD_ASSERT(input.eof());

            fwrite(std::move(updates));
        }

        size_t parse_accounts(byte_string_view in, UpdateList &account_updates)
        {
            constexpr auto account_fixed_size =
                sizeof(bytes32_t) + sizeof(uint256_t) + sizeof(uint64_t) +
                sizeof(bytes32_t) + sizeof(uint64_t);
            static_assert(account_fixed_size == 112);
            size_t total_processed = 0;
            while (in.size() >= account_fixed_size) {
                constexpr auto num_storage_offset =
                    account_fixed_size - sizeof(uint64_t);
                auto const num_storage = unaligned_load<uint64_t>(
                    in.substr(num_storage_offset, sizeof(uint64_t)).data());
                auto const storage_size = num_storage * storage_entry_size;
                auto const entry_size = account_fixed_size + storage_size;
                MONAD_ASSERT(entry_size <= buf_size_);
                if (in.size() < entry_size) {
                    return total_processed;
                }
                auto &update = update_alloc_.emplace_back(handle_account(in));
                if (num_storage) {
                    update.next = handle_storage(
                        in.substr(account_fixed_size, storage_size));
                }
                account_updates.push_front(update);
                total_processed += entry_size;
                in = in.substr(entry_size);
            }
            return total_processed;
        }

        size_t parse_code(byte_string_view in, UpdateList &code_updates)
        {
            constexpr auto hash_and_len_size =
                sizeof(bytes32_t) + sizeof(uint64_t);
            static_assert(hash_and_len_size == 40);
            size_t total_processed = 0;
            while (in.size() >= hash_and_len_size) {
                auto const code_len = unaligned_load<uint64_t>(
                    in.substr(sizeof(bytes32_t), sizeof(uint64_t)).data());
                auto const entry_size = code_len + hash_and_len_size;
                MONAD_ASSERT(entry_size <= buf_size_);
                if (in.size() < entry_size) {
                    return total_processed;
                }
                code_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = in.substr(0, sizeof(bytes32_t)),
                    .value = in.substr(hash_and_len_size, code_len),
                    .incarnation = false,
                    .next = UpdateList{}}));

                total_processed += entry_size;
                in = in.substr(entry_size);
            }
            return total_processed;
        }

        Update handle_account(byte_string_view curr)
        {
            constexpr auto balance_offset = sizeof(bytes32_t);
            constexpr auto nonce_offset = balance_offset + sizeof(uint256_t);
            constexpr auto code_hash_offset = nonce_offset + sizeof(uint64_t);

            return Update{
                .key = curr.substr(0, sizeof(bytes32_t)),
                .value = bytes_alloc_.emplace_back(rlp::encode_account(Account{
                    .balance = unaligned_load<uint256_t>(
                        curr.substr(balance_offset, sizeof(uint256_t)).data()),
                    .code_hash = unaligned_load<bytes32_t>(
                        curr.substr(code_hash_offset, sizeof(bytes32_t))
                            .data()),
                    .nonce = unaligned_load<uint64_t>(
                        curr.substr(nonce_offset, sizeof(uint64_t)).data())})),
                .incarnation = false,
                .next = UpdateList{}};
        }

        UpdateList handle_storage(byte_string_view in)
        {
            UpdateList storage_updates;
            while (!in.empty()) {
                storage_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = in.substr(0, sizeof(bytes32_t)),
                    .value = rlp::zeroless_view(
                        in.substr(sizeof(bytes32_t), sizeof(bytes32_t))),
                    .incarnation = false,
                    .next = UpdateList{}}));
                in = in.substr(storage_entry_size);
            }
            return storage_updates;
        }
    };
}

std::unique_ptr<StateMachine> InMemoryMachine::clone() const
{
    return std::make_unique<InMemoryMachine>(*this);
}

void Machine::down(unsigned char const nibble)
{
    ++depth;
    MONAD_ASSERT(depth <= max_depth);
    MONAD_ASSERT(
        (nibble == state_nibble || nibble == code_nibble ||
         nibble == receipt_nibble) ||
        depth != prefix_len + BLOCK_NUM_NIBBLES_LEN);
    if (MONAD_UNLIKELY(depth == prefix_len + BLOCK_NUM_NIBBLES_LEN)) {
        MONAD_ASSERT(trie_section == TrieType::Prefix);
        if (nibble == state_nibble) {
            trie_section = TrieType::State;
        }
        else if (nibble == receipt_nibble) {
            trie_section = TrieType::Receipt;
        }
        else {
            trie_section = TrieType::Code;
        }
    }
}

void Machine::up(size_t const n)
{
    MONAD_ASSERT(n <= depth);
    depth -= static_cast<uint8_t>(n);
    if (MONAD_UNLIKELY(depth < prefix_len + BLOCK_NUM_NIBBLES_LEN)) {
        trie_section = TrieType::Prefix;
    }
}

Compute &Machine::get_compute() const
{
    static EmptyCompute empty_compute;
    static MerkleCompute state_compute;
    static RootMerkleCompute state_root_compute;
    static VarLenMerkleCompute receipt_compute;
    static RootVarLenMerkleCompute receipt_root_compute;

    if (MONAD_LIKELY(trie_section == TrieType::State)) {
        return depth == prefix_len + BLOCK_NUM_NIBBLES_LEN ? state_root_compute
                                                           : state_compute;
    }
    else if (trie_section == TrieType::Receipt) {
        return depth == prefix_len + BLOCK_NUM_NIBBLES_LEN
                   ? receipt_root_compute
                   : receipt_compute;
    }
    else {
        return empty_compute;
    }
}

bool InMemoryMachine::cache() const
{
    return true;
}

bool InMemoryMachine::compact() const
{
    return false;
}

std::unique_ptr<StateMachine> OnDiskMachine::clone() const
{
    return std::make_unique<OnDiskMachine>(*this);
}

bool OnDiskMachine::cache() const
{
    return depth <= cache_depth;
}

bool OnDiskMachine::compact() const
{
    return depth >= BLOCK_NUM_NIBBLES_LEN;
}

TrieDb::TrieDb(std::optional<mpt::OnDiskDbConfig> const &config)
    : machine_{[&] -> std::unique_ptr<Machine> {
        if (config.has_value()) {
            return std::make_unique<OnDiskMachine>();
        }
        return std::make_unique<InMemoryMachine>();
    }()}
    , db_{config.has_value() ? mpt::Db{*machine_, config.value()}
                             : mpt::Db{*machine_}}
    , curr_block_id_{[&] {
        if (config.has_value()) {
            if (config->start_block_id.has_value()) {
                // throw error on invalid block number in config
                if (!db_.get_latest_block_id().has_value() ||
                    !db_.get_earliest_block_id().has_value()) {
                    throw std::runtime_error(
                        "No valid history in existing db to resume from");
                }
                if (config->start_block_id >
                        db_.get_latest_block_id().value() ||
                    config->start_block_id <
                        db_.get_earliest_block_id().value()) {
                    throw std::runtime_error(fmt::format(
                        "Invalid starting block id to resume, the valid block "
                        "id range is [{}, {}]",
                        db_.get_earliest_block_id().value(),
                        db_.get_latest_block_id().value()));
                }
                return config->start_block_id.value();
            }
            return db_.get_latest_block_id().value_or(0);
        }
        // in memory triedb block id remains 0
        return 0ul;
    }()}
    , is_on_disk_{config.has_value()}
{
}

TrieDb::TrieDb(
    std::optional<mpt::OnDiskDbConfig> const &config, std::istream &input,
    uint64_t const init_block_number, size_t const batch_size)
    : TrieDb{config}
{
    if (db_.root().is_valid()) {
        throw std::runtime_error(
            "Unable to load snapshot to an existing db, truncate the "
            "existing db to empty and try again");
    }
    if (is_on_disk_) {
        curr_block_id_ = init_block_number;
    } // was init to 0 and will remain 0 for in memory db
    boost::json::basic_parser<JsonDbLoader> parser{
        boost::json::parse_options{}, db_, batch_size, curr_block_id_};

    char buf[4096];
    std::error_code ec;
    while (input.read(buf, sizeof(buf))) {
        auto const count = static_cast<size_t>(input.gcount());
        MONAD_ASSERT(count <= sizeof(buf));
        parser.write_some(true, buf, count, ec);
        MONAD_ASSERT(!ec);
    }
    auto const count = static_cast<size_t>(input.gcount());
    MONAD_ASSERT(count <= sizeof(buf));
    parser.write_some(false, buf, count, ec);
    MONAD_ASSERT(!ec);
    MONAD_ASSERT(input.eof());
    MONAD_ASSERT(parser.done());

    parser.handler().write();
    MONAD_ASSERT(
        machine_->depth == 0 &&
        machine_->trie_section == Machine::TrieType::Prefix);
}

TrieDb::TrieDb(
    std::optional<mpt::OnDiskDbConfig> const &config, std::istream &accounts,
    std::istream &code, uint64_t const init_block_number, size_t const buf_size)
    : TrieDb{config}
{
    if (db_.root().is_valid()) {
        throw std::runtime_error(
            "Unable to load snapshot to an existing db, truncate the "
            "existing db to empty and try again");
    }
    if (is_on_disk_) {
        curr_block_id_ = init_block_number;
    } // was init to 0 and will remain 0 for in memory db
    BinaryDbLoader loader{db_, buf_size, curr_block_id_};
    loader.load(accounts, code);
}

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    auto const value = db_.get(
        concat(state_nibble, NibblesView{to_key(addr)}), curr_block_id_);
    if (!value.has_value()) {
        return std::nullopt;
    }

    auto encoded_account = value.value();
    auto acct = rlp::decode_account(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    MONAD_DEBUG_ASSERT(encoded_account.empty());
    acct.value().incarnation = 0;
    return acct.value();
}

bytes32_t TrieDb::read_storage(Address const &addr, bytes32_t const &key)
{
    auto const value = db_.get(
        concat(
            state_nibble, NibblesView{to_key(addr)}, NibblesView{to_key(key)}),
        curr_block_id_);
    if (!value.has_value()) {
        return {};
    }
    MONAD_ASSERT(value.value().size() <= sizeof(bytes32_t));
    bytes32_t ret;
    std::copy_n(
        value.value().begin(),
        value.value().size(),
        ret.bytes + sizeof(bytes32_t) - value.value().size());
    return ret;
};

std::shared_ptr<CodeAnalysis> TrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read code analysis object
    auto const value = db_.get(
        concat(code_nibble, NibblesView{to_byte_string_view(code_hash.bytes)}),
        curr_block_id_);
    if (!value.has_value()) {
        return std::make_shared<CodeAnalysis>(analyze({}));
    }
    return std::make_shared<CodeAnalysis>(analyze(value.assume_value()));
}

void TrieDb::commit(
    StateDeltas const &state_deltas, Code const &code,
    std::vector<Receipt> const &receipts)
{
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
                            .key = NibblesView{bytes_alloc_.emplace_back(
                                to_key(key))},
                            .value =
                                delta.second == bytes32_t{}
                                    ? std::nullopt
                                    : std::make_optional(rlp::zeroless_view(
                                          to_byte_string_view(
                                              delta.second.bytes))),
                            .incarnation = false,
                            .next = UpdateList{}}));
                }
            }
            value =
                bytes_alloc_.emplace_back(rlp::encode_account(account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = NibblesView{bytes_alloc_.emplace_back(to_key(addr))},
                .value = value,
                .incarnation = account.has_value()
                                   ? account.value().incarnation != 0
                                   : false,
                .next = std::move(storage_updates)}));
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
            .next = UpdateList{}}));
    }

    UpdateList receipt_updates;
    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &receipt = receipts[i];
        receipt_updates.push_front(update_alloc_.emplace_back(Update{
            .key =
                NibblesView{bytes_alloc_.emplace_back(rlp::encode_unsigned(i))},
            .value = bytes_alloc_.emplace_back(rlp::encode_receipt(receipt)),
            .incarnation = false,
            .next = UpdateList{}}));
    }
    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates)};
    auto receipt_update = Update{
        .key = receipt_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(receipt_updates)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(receipt_update);
    db_.upsert(std::move(updates), curr_block_id_);
    MONAD_ASSERT(machine_->trie_section == Machine::TrieType::Prefix);

    update_alloc_.clear();
    bytes_alloc_.clear();
}

void TrieDb::increment_block_number()
{
    if (is_on_disk_) {
        ++curr_block_id_;
    }
}

void TrieDb::create_and_prune_block_history(uint64_t) const {

};

bytes32_t TrieDb::state_root()
{
    auto const value = db_.get_data(state_nibbles, curr_block_id_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

bytes32_t TrieDb::receipts_root()
{
    auto const value = db_.get_data(receipt_nibbles, curr_block_id_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

nlohmann::json TrieDb::to_json()
{
    struct Traverse : public TraverseMachine
    {
        TrieDb &db;
        nlohmann::json json;
        Nibbles path;

        Traverse(TrieDb &db)
            : db(db)
            , json(nlohmann::json::object())
            , path()
        {
        }

        virtual void down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
                return;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (path.nibble_size() == (KECCAK256_SIZE * 2)) {
                handle_account(node);
            }
            else if (
                path.nibble_size() == ((KECCAK256_SIZE + KECCAK256_SIZE) * 2)) {
                handle_storage(node);
            }
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
            auto acct = rlp::decode_account(encoded_account);
            MONAD_DEBUG_ASSERT(!acct.has_error());
            MONAD_DEBUG_ASSERT(encoded_account.empty());

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["balance"] = fmt::format("{}", acct.value().balance);
            json[key]["nonce"] = fmt::format("0x{:x}", acct.value().nonce);

            auto const code_analysis = db.read_code(acct.value().code_hash);
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
            MONAD_ASSERT(node.value().size() <= sizeof(bytes32_t));

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            auto const key = fmt::format(
                "{}",
                NibblesView{path}.substr(
                    KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

            bytes32_t value;
            std::copy_n(
                node.value().begin(),
                node.value().size(),
                value.bytes + sizeof(bytes32_t) - node.value().size());

            json[acct_key]["storage"][key] = fmt::format(
                "0x{:02x}",
                fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        }
    } traverse(*this);

    db_.traverse(state_nibbles, traverse, curr_block_id_);

    return traverse.json;
}

uint64_t TrieDb::current_block_number() const
{
    return curr_block_id_;
}

MONAD_DB_NAMESPACE_END
