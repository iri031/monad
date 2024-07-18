#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>
#include <monad/execution/trace/call_trace.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>

#include <optional>

using namespace monad;

namespace
{
    constexpr auto rev = EVMC_SHANGHAI;
    uint8_t const input[] = {'i', 'n', 'p', 'u', 't'};
    uint8_t const output[] = {'o', 'u', 't', 'p', 'u', 't'};
    static Transaction const tx{.gas_limit = 10'000u};

    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
}

TEST(CallFrame, to_json)
{
    CallFrame call_frame{
        .type = EVMC_CALL,
        .from = a,
        .to = std::make_optional(b),
        .value = 20'901u,
        .gas = 100'000u,
        .gas_used = 21'000u,
        .input = byte_string{},
        .status = EVMC_SUCCESS,
    };

    auto const json_str = R"(
    {
        "from":"0x5353535353535353535353535353535353535353",
        "gas":"0x186a0",
        "gasUsed":"0x5208",
        "input":"0x",
        "to":"0xbebebebebebebebebebebebebebebebebebebebe",
        "type":"CALL",
        "value":"0x51a5"
    })";

    EXPECT_EQ(call_frame.to_json(), nlohmann::json::parse(json_str));
}

TEST(CallTrace, enter_and_exit_simple)
{
    static evmc_message msg{.input_data = input};
    static evmc::Result res{};
    res.output_data = output;

    CallTracer call_tracer{0, tx};
    {
        msg.depth = 0;
        call_tracer.on_enter<rev>(msg);
        {
            msg.depth = 1;
            call_tracer.on_enter<rev>(msg);
            call_tracer.on_exit<rev>(res);
        }
        call_tracer.on_exit<rev>(res);
    }

    auto const call_frames = call_tracer.get_call_frames();
    EXPECT_EQ(call_frames.size(), 1);
    EXPECT_EQ(call_frames.back().calls.size(), 1);
}

TEST(CallTrace, enter_and_exit)
{
    static evmc_message msg{.input_data = input};
    static evmc::Result res{};
    res.output_data = output;

    CallTracer call_tracer{1, tx};
    {
        msg.depth = 0;
        call_tracer.on_enter<rev>(msg);
        {
            msg.depth = 1;
            call_tracer.on_enter<rev>(msg);
            call_tracer.on_exit<rev>(res);

            call_tracer.on_enter<rev>(msg);
            {
                msg.depth = 2;
                call_tracer.on_enter<rev>(msg);
                {
                    msg.depth = 3;
                    call_tracer.on_enter<rev>(msg);
                    call_tracer.on_exit<rev>(res);

                    call_tracer.on_enter<rev>(msg);
                    call_tracer.on_exit<rev>(res);
                }
                msg.depth = 2;
                call_tracer.on_exit<rev>(res);

                call_tracer.on_enter<rev>(msg);
                call_tracer.on_exit<rev>(res);
            }
            msg.depth = 1;
            call_tracer.on_exit<rev>(res);

            call_tracer.on_enter<rev>(msg);
            call_tracer.on_exit<rev>(res);
        }
        msg.depth = 0;
        call_tracer.on_exit<rev>(res);

        call_tracer.on_enter<rev>(msg);
        call_tracer.on_exit<rev>(res);
    }

    auto const call_frames = call_tracer.get_call_frames();
    EXPECT_EQ(call_frames.size(), 2);
    EXPECT_EQ(call_frames[1].calls.size(), 0);

    auto const &child_frames = call_frames[0].calls;
    EXPECT_EQ(child_frames.size(), 3);
    EXPECT_EQ(child_frames[0].calls.size(), 0);
    EXPECT_EQ(child_frames[2].calls.size(), 0);

    auto const &grandchild_frames = child_frames[1].calls;
    EXPECT_EQ(grandchild_frames.size(), 2);
    EXPECT_EQ(grandchild_frames[1].calls.size(), 0);

    auto const &greatgrandchild_frames = grandchild_frames[0].calls;
    EXPECT_EQ(greatgrandchild_frames.size(), 2);
    EXPECT_EQ(greatgrandchild_frames[0].calls.size(), 0);
    EXPECT_EQ(greatgrandchild_frames[1].calls.size(), 0);
}
