#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/trace/call_trace.hpp>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>

#include <fstream>
#include <iomanip>
#include <optional>
#include <span>
#include <sstream>
#include <string>

MONAD_NAMESPACE_BEGIN

std::string evmc_call_to_string(evmc_call_kind const &type)
{
    switch (type) {
    case EVMC_CALL:
        return "CALL";
    case EVMC_DELEGATECALL:
        return "DELEGATECALL";
    case EVMC_CALLCODE:
        return "CALLCODE";
    case EVMC_CREATE:
        return "CREATE";
    case EVMC_CREATE2:
        return "CREATE2";
    default:
        std::unreachable();
    }
}

std::string to_hex_string(byte_string_view const &view)
{
    std::stringstream ss;
    ss << std::hex;

    ss << "0x";

    for (unsigned i = 0; i < view.length(); ++i) {
        ss << std::setw(2) << std::setfill('0') << static_cast<int>(view[i]);
    }

    return ss.str();
}

nlohmann::json CallFrame::to_json() const
{
    nlohmann::json res{};
    res["type"] = evmc_call_to_string(type);
    res["from"] = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(from.bytes)), ""));
    // TODO: need to verify if it's correct to omit "to" on create/create2
    if (to.has_value()) {
        res["to"] = fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(to.value().bytes)), ""));
    }
    // DITTO
    if (value.has_value()) {
        res["value"] = "0x" + intx::to_string(value.value(), 16);
    }
    res["gas"] = fmt::format("0x{:x}", gas);
    res["gasUsed"] = fmt::format("0x{:x}", gas_used);
    res["input"] = to_hex_string(input);

    if (output.has_value()) {
        res["output"] = to_hex_string(output.value());
    }

    // If status == EVMC_SUCCESS, no error field is shown
    if (status == EVMC_REVERT) {
        res["error"] = "REVERT";
    }
    else if (status != EVMC_SUCCESS) {
        res["error"] = "ERROR"; // TODO: generic error for now
    }

    if (!calls.empty()) {
        res["calls"] = nlohmann::json::array();
        for (unsigned i = 0; i < calls.size(); ++i) {
            nlohmann::json obj = nlohmann::json::object();
            res["calls"].push_back(obj);
        }
    }

    return res;
}

CallTracer::CallTracer(
    uint64_t const block_number, Transaction const &tx, bool only_top)
    : only_top_(only_top)
    , call_frames_{}
    , depth_{0}
    , block_number_(block_number)
    , tx_(tx)
    , tx_hash_(keccak256(rlp::encode_transaction(tx)))
{
}

void CallTracer::to_json_helper(
    nlohmann::json &json, CallFrame const &call_frame) const
{
    json = call_frame.to_json();

    if (call_frame.calls.empty()) {
        return;
    }
    MONAD_ASSERT(json.contains("calls"));
    for (unsigned i = 0; i < call_frame.calls.size(); ++i) {
        to_json_helper(json["calls"][i], call_frame.calls[i]);
    }
}

nlohmann::json CallTracer::to_json() const
{
    MONAD_ASSERT(!call_frames_.empty());

    nlohmann::json res{};
    auto const key = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(tx_hash_.bytes)), ""));
    nlohmann::json value{};
    to_json_helper(value, call_frames_[0]);
    res[key] = value;

    return res;
}

void CallTracer::to_file() const
{
    QUILL_LOG_INFO(quill::get_logger("call_trace"), "{}", to_json().dump());
}

MONAD_NAMESPACE_END
