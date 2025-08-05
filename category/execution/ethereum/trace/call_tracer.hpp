#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <optional>
#include <span>
#include <stack>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Receipt;
struct Transaction;

struct CallTracerBase
{
    virtual ~CallTracerBase() = default;

    virtual void on_enter(evmc_message const &) = 0;
    virtual void on_exit(evmc::Result const &) = 0;
    virtual void on_self_destruct(Address const &from, Address const &to) = 0;
    virtual void on_finish(uint64_t const) = 0;
    virtual void reset() = 0;
};

struct NoopCallTracer final : public CallTracerBase
{
    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void on_self_destruct(Address const &, Address const &) override;
    virtual void on_finish(uint64_t const) override;
    virtual void reset() override;
};

class CallTracer final : public CallTracerBase
{
    std::vector<CallFrame> &frames_;
    std::stack<size_t> last_;
    uint64_t depth_;
    Transaction const &tx_;

public:
    CallTracer() = delete;
    CallTracer(CallTracer const &) = delete;
    CallTracer(CallTracer &&) = delete;
    CallTracer(Transaction const &, std::vector<CallFrame> &);

    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void
    on_self_destruct(Address const &from, Address const &to) override;
    virtual void on_finish(uint64_t const) override;
    virtual void reset() override;

    nlohmann::json to_json() const;
};

MONAD_NAMESPACE_END
