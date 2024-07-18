#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <ethash/hash_types.hpp>

#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>

#include <filesystem>
#include <optional>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    inline constexpr uint64_t g_star(
        evmc_revision const &rev, uint64_t const gas_limit,
        uint64_t const gas_remaining, uint64_t const refund)
    {
        // EIP-3529
        auto const max_refund_quotient = rev >= EVMC_LONDON ? 5u : 2u;
        auto const refund_allowance =
            (gas_limit - gas_remaining) / max_refund_quotient;

        return gas_remaining + std::min(refund_allowance, refund);
    }
}

struct CallFrame
{
    evmc_call_kind type;
    Address from;
    std::optional<Address> to{std::nullopt};
    std::optional<uint256_t> value{std::nullopt}; // amount of value transfer
    uint64_t gas;
    uint64_t gas_used{0};
    byte_string input{};
    std::optional<byte_string> output{std::nullopt};
    evmc_status_code status{EVMC_SUCCESS};

    std::vector<CallFrame> calls{};

    // TODO: official documentation doesn't contain "logs", but geth/reth
    // implementation does

    nlohmann::json to_json() const; // key = hash(tx)

    uint64_t depth; // needed for internal tracking
};

class CallTracer
{
    bool only_top_;
    std::vector<CallFrame> call_frames_;
    uint64_t depth_;

    uint64_t block_number_;
    Transaction const &tx_;
    hash256 tx_hash_;

    uint64_t intrinsic_gas_{0};

    std::filesystem::path const trace_dir_{
        std::filesystem::current_path() /
        "call_trace"}; // TODO: make it configurable

public:
    /*
        block_number: needed to write to specific file
        tx: needed to compute hash
    */
    CallTracer() = delete;
    CallTracer(CallTracer const &) = delete;
    CallTracer(CallTracer &&) = delete;

    explicit CallTracer(
        uint64_t const block_number, Transaction const &,
        bool only_top = false);

    nlohmann::json to_json() const;
    void to_file() const;

    // called when entering a new frame
    template <evmc_revision rev>
    void on_enter(evmc_message const &msg)
    {
        depth_ = static_cast<uint64_t>(msg.depth);

        uint64_t gas = 0;
        if (call_frames_.empty()) {
            intrinsic_gas_ = intrinsic_gas<rev>(tx_);
            gas = intrinsic_gas_;
        }

        if (MONAD_UNLIKELY(msg.depth >= 1 && only_top_)) {
            return;
        }

        // TODO: This is to conform with quicknode RPC, but I am skeptical of
        // its correctness
        Address from = msg.sender;
        if (msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE) {
            from = msg.recipient;
        }

        std::optional<Address> to = std::nullopt;
        if (msg.kind == EVMC_CALL) {
            to = std::make_optional(msg.recipient);
        }
        else if (msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE) {
            to = std::make_optional(msg.code_address);
        }

        CallFrame call_frame{
            .type = msg.kind,
            .from = from,
            .to = to,
            .value = intx::be::load<uint256_t>(msg.value),
            .gas = static_cast<uint64_t>(msg.gas) + gas,
            .input = msg.input_data == nullptr
                         ? byte_string{}
                         : byte_string{msg.input_data, msg.input_size},
            .depth = static_cast<uint64_t>(msg.depth),
        };

        if (msg.depth == 0) {
            call_frames_.emplace_back(std::move(call_frame));
            return;
        }

        MONAD_ASSERT(!call_frames_.empty());
        auto *last_frame = &call_frames_.back();
        for (int i = 1; i < msg.depth; ++i) {
            last_frame = &last_frame->calls.back();
        }
        MONAD_DEBUG_ASSERT(
            last_frame->depth + 1 == static_cast<uint64_t>(msg.depth));
        last_frame->calls.emplace_back(call_frame);
    }

    // called when exiting the current frame
    template <evmc_revision rev>
    void on_exit(evmc::Result const &res)
    {
        MONAD_ASSERT(!call_frames_.empty());

        auto *last_frame = &call_frames_.back();
        for (unsigned i = 0; i < depth_; ++i) {
            last_frame = &last_frame->calls.back();
        }

        auto const gas_limit = last_frame->gas;
        auto const gas_remaining = g_star(
            rev,
            gas_limit,
            static_cast<uint64_t>(res.gas_left),
            static_cast<uint64_t>(res.gas_refund));
        auto const gas_used = gas_limit - gas_remaining;
        last_frame->gas_used = gas_used;

        if (res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT) {
            last_frame->output = res.output_data == nullptr
                                     ? std::nullopt
                                     : std::make_optional(byte_string{
                                           res.output_data, res.output_size});
        }
        last_frame->status = res.status_code;
        depth_--;
    }

    // debug helper
    std::vector<CallFrame> get_call_frames() const
    {
        return call_frames_;
    }

private:
    void to_json_helper(nlohmann::json &, CallFrame const &) const;
};

MONAD_NAMESPACE_END
