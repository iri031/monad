// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/data.hpp>
#include <category/vm/fuzzing/generator/instruction_data.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <array>
#include <limits>
#include <memory>
#include <random>
#include <unordered_set>
#include <variant>
#include <vector>

using namespace evmc::literals;

namespace monad::vm::fuzzing
{
    enum class GeneratorFocus
    {
        Generic,
        Pow2,
        DynJump
    };

    struct ValidAddress
    {
        std::optional<evmc::address> address;
    };

    struct ValidJumpDest
    {
    };

    struct BasicBlockInfo
    {
        bool is_main;
        bool is_exit;
        bool is_jump_dest;
    };

    struct Constant
    {
        runtime::uint256_t value;
    };

    template <typename Engine>
    Constant meaningful_constant(Engine &gen)
    {
        static constexpr auto values = std::array<runtime::uint256_t, 4>{
            0,
            1,
            exp(runtime::uint256_t(2), runtime::uint256_t(255)),
            std::numeric_limits<runtime::uint256_t>::max(),
        };

        return Constant{uniform_sample(gen, values)};
    }

    template <typename Engine>
    Constant small_constant(Engine &gen)
    {
        // For testing byte,signextend,shifts
        auto dist = std::uniform_int_distribution(0, 257);
        return Constant{dist(gen)};
    }

    template <typename Engine>
    Constant power_of_32_constant(Engine &gen)
    {
        // Special power of two constants for boundary cases in
        // mulmod/addmod/mul/div/sdiv/mod/smod optimization
        auto dist = std::uniform_int_distribution(1, 8);
        auto shift = 32 * dist(gen);
        return Constant{runtime::uint256_t{1} << shift};
    }

    template <typename Engine>
    Constant negated_power_of_32_constant(Engine &gen)
    {
        // Special boundary cases for mul/sdiv/smod optimization
        return Constant{-power_of_32_constant(gen).value};
    }

    template <typename Engine>
    Constant power_of_two_constant(Engine &gen)
    {
        // To trigger mulmod/addmod/mul/div/sdiv/mod/smod optimization
        auto dist = std::uniform_int_distribution(1, 254);
        return Constant{
            exp(runtime::uint256_t(2), runtime::uint256_t(dist(gen)))};
    }

    template <typename Engine>
    Constant negated_power_of_two_constant(Engine &gen)
    {
        // To trigger mul/sdiv/smod optimization
        return Constant{-power_of_two_constant(gen).value};
    }

    template <typename Engine>
    std::uint32_t random_uint32(Engine &gen)
    {
        auto dist = std::uniform_int_distribution<std::uint32_t>();
        return dist(gen);
    }

    template <std::size_t Bits = 256, typename Engine = void>
    Constant random_constant(Engine &gen)
        requires(Bits % 64 == 0 && Bits > 0 && Bits <= 256)
    {
        static constexpr auto words = Bits / 64;
        auto dist =
            std::uniform_int_distribution<runtime::uint256_t::word_type>();

        return Constant{runtime::uint256_t{
            words >= 0 ? dist(gen) : 0,
            words >= 1 ? dist(gen) : 0,
            words >= 2 ? dist(gen) : 0,
            words >= 3 ? dist(gen) : 0,
        }};
    }

    template <typename Engine>
    evmc::address random_address(Engine &eng)
    {
        auto ret = evmc::address{};
        auto const value = random_constant<192>(eng);

        auto const *bytes = intx::as_bytes(value.value);
        std::copy_n(bytes, 20, &ret.bytes[0]);

        return ret;
    }

    template <typename Engine>
    Constant random_constant_with_cleared_words(Engine &gen)
    {
        // To trigger inline mul optimization
        auto c = random_constant(gen);
        for (size_t i = 0; i < 4; ++i) {
            with_probability(gen, 0.5, [&](auto &) { c.value[i] = 0; });
        }
        return c;
    }

    template <typename Engine>
    Constant memory_constant(Engine &gen)
    {
        auto dist = std::uniform_int_distribution<std::uint64_t>(0, 1 << 16);
        return Constant{dist(gen)};
    }

    template <typename Engine>
    evmc::address generate_precompile_address(Engine &eng, evmc_revision rev)
    {
        std::uniform_int_distribution<uint8_t> dist(1, num_precompiles(rev));
        evmc::address addr{};
        addr.bytes[sizeof(evmc::address) - 1] = dist(eng);
        return addr;
    }

    template <typename Engine>
    evmc::address generate_address(
        Engine &eng, evmc_revision rev,
        std::vector<evmc::address> const &valid_addresses)
    {
        auto const &addr = [&] {
            if (valid_addresses.empty()) {
                return generate_precompile_address(eng, rev);
            }
            return discrete_choice<evmc::address>(
                eng,
                [&](auto &g) { return uniform_sample(g, valid_addresses); },
                Choice(0.001, [rev](auto &g) {
                    return generate_precompile_address(g, rev);
                }));
        }();

        return addr;
    }

    using Push = std::variant<ValidAddress, ValidJumpDest, Constant>;

    template <typename Engine>
    Push generate_push(
        GeneratorFocus focus, Engine &eng,
        std::vector<evmc::address> const &valid_addresses)
    {
        double valid_jumpdest_prob = 0.0;
        double valid_address_prob = 0.0;
        double random_constant_with_cleared_words_prob = 0.0;
        double meaningful_constant_prob = 0.0;
        double small_constant_prob = 0.0;
        double power_of_two_constant_prob = 0.0;
        double power_of_32_constant_prob = 0.0;
        double negated_power_of_32_constant_prob = 0.0;
        double negated_power_of_two_constant_prob = 0.0;
        switch (focus) {
        case GeneratorFocus::Generic:
            valid_jumpdest_prob = 0.25;
            valid_address_prob = 0.10;
            random_constant_with_cleared_words_prob = 0.10;
            meaningful_constant_prob = 0.10;
            small_constant_prob = 0.10;
            power_of_two_constant_prob = 0.10;
            power_of_32_constant_prob = 0.10;
            negated_power_of_32_constant_prob = 0.05;
            negated_power_of_two_constant_prob = 0.05;
            break;
        case GeneratorFocus::Pow2:
            power_of_two_constant_prob = 0.25;
            power_of_32_constant_prob = 0.25;
            negated_power_of_32_constant_prob = 0.15;
            negated_power_of_two_constant_prob = 0.15;
            break;
        case GeneratorFocus::DynJump:
            valid_jumpdest_prob = 0.50;
            small_constant_prob = 0.20;
            meaningful_constant_prob = 0.20;
            break;
        }
        return discrete_choice<Push>(
            eng,
            [](auto &g) { return random_constant(g); },
            Choice(valid_jumpdest_prob, [](auto &) { return ValidJumpDest{}; }),
            Choice(
                valid_address_prob,
                [&](auto &) {
                    if (valid_addresses.empty()) {
                        return ValidAddress{};
                    } else {
                        return ValidAddress{
                            uniform_sample(eng, valid_addresses)};
                    }
                }),
            Choice(
                random_constant_with_cleared_words_prob,
                [](auto &g) { return random_constant_with_cleared_words(g); }),
            Choice(
                meaningful_constant_prob,
                [](auto &g) { return meaningful_constant(g); }),
            Choice(
                small_constant_prob, [](auto &g) { return small_constant(g); }),
            Choice(
                power_of_two_constant_prob,
                [](auto &g) { return power_of_two_constant(g); }),
            Choice(
                power_of_32_constant_prob,
                [](auto &g) { return power_of_32_constant(g); }),
            Choice(
                negated_power_of_32_constant_prob,
                [](auto &g) { return negated_power_of_32_constant(g); }),
            Choice(negated_power_of_two_constant_prob, [](auto &g) {
                return negated_power_of_two_constant(g);
            }));
    }

    template <typename Engine>
    Push generate_calldata_item(
        GeneratorFocus focus, Engine &eng,
        std::vector<evmc::address> const &valid_addresses)
    {
        return std::visit(
            Cases{
                [&](ValidJumpDest) -> Push { return random_constant(eng); },
                [](Push const &x) -> Push { return x; }},
            generate_push(focus, eng, valid_addresses));
    }

    struct Call
    {
        std::uint8_t opcode;
        uint8_t gasPct;
        uint8_t balancePct;
        Constant argsOffset;
        Constant argsSize;
        Constant retOffset;
        Constant retSize;
        evmc::address address;
        bool isTrivial;
    };

    template <typename Engine>
    Call generate_call(
        Engine &eng, evmc_revision rev,
        std::vector<evmc::address> const &valid_addresses)
    {
        static constexpr auto pcts =
            std::array<uint8_t, 12>{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11};
        auto r = Call{
            .opcode = uniform_sample(eng, call_non_terminators),
            .gasPct = uniform_sample(eng, pcts),
            .balancePct = uniform_sample(eng, pcts),
            .argsOffset = memory_constant(eng),
            .argsSize = memory_constant(eng),
            .retOffset = memory_constant(eng),
            .retSize = memory_constant(eng),
            .address = generate_address(eng, rev, valid_addresses),
            .isTrivial = false};
        with_probability(eng, 0.05, [&](auto &) { r.isTrivial = true; });
        return r;
    }

    struct ReturnDataCopy
    {
        Constant destOffset;
        uint8_t sizePct; // percent of return data size
        uint8_t offsetPct; // percent of return data size
        bool isTrivial; // sometimes just emit a simple RETURNDATACOPY
    };

    template <typename Engine>
    ReturnDataCopy generate_returndatacopy(Engine &eng)
    {
        auto r = ReturnDataCopy{
            .destOffset = memory_constant(eng),
            .sizePct = 10, // mostly 10, sometimes < 0..9, rarely 11
            .offsetPct = 0, // mostly 0, sometimes < 1..9, rarely 10
            .isTrivial = false,
        };
        with_probability(eng, 0.05, [&](auto &) {
            auto dist = std::uniform_int_distribution(0, 9);
            r.sizePct = static_cast<uint8_t>(dist(eng));
        });
        with_probability(eng, 0.0005, [&](auto &) { r.sizePct = 11; });

        with_probability(eng, 0.05, [&](auto &) {
            auto dist = std::uniform_int_distribution(1, 9);
            r.offsetPct = static_cast<uint8_t>(dist(eng));
        });
        with_probability(eng, 0.0005, [&](auto &) { r.offsetPct = 10; });
        with_probability(eng, 0.05, [&](auto &) { r.isTrivial = true; });

        return r;
    }

    struct Create
    {
        std::uint8_t opcode;
        uint8_t balancePct;
        Constant offset;
        Constant salt;
        evmc::address address;
        bool isTrivial; // sometimes just emit a simple CREATE/CREATE2
    };

    template <typename Engine>
    Create generate_create(
        Engine &eng, evmc_revision rev,
        std::vector<evmc::address> const &valid_addresses)
    {
        static constexpr auto create_non_terminators = std::array{
            CREATE,
            CREATE2,
        };

        static constexpr auto pcts =
            std::array<uint8_t, 12>{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11};

        auto r = Create{
            .opcode = uniform_sample(eng, create_non_terminators),
            .balancePct = uniform_sample(eng, pcts),
            .offset = memory_constant(eng),
            .salt = random_constant(eng),
            .address = generate_address(eng, rev, valid_addresses),
            .isTrivial = false,
        };

        with_probability(eng, 0.05, [&](auto &) { r.isTrivial = true; });
        return r;
    }

    struct NonTerminator
    {
        std::uint8_t opcode;
        std::vector<std::pair<std::uint8_t, Constant>> opnds = {};
    };

    struct Terminator
    {
        std::uint8_t opcode;
        std::vector<std::pair<std::uint8_t, Constant>> opnds = {};
    };

    using Instruction = std::variant<
        NonTerminator, Terminator, Push, Call, ReturnDataCopy, Create>;

    template <typename Engine>
    NonTerminator
    generate_non_terminator(Engine &eng, std::uint8_t const opcode)
    {
        std::vector<std::pair<std::uint8_t, Constant>> mem_opnds;
        for (auto mem_op : memory_operands(opcode)) {
            with_probability(eng, 0.95, [&](auto &) {
                auto const safe_value = memory_constant(eng);
                mem_opnds.push_back({mem_op, safe_value});
            });
        }
        return NonTerminator{opcode, std::move(mem_opnds)};
    }

    template <typename Engine>
    NonTerminator generate_common_non_terminator(Engine &eng)
    {
        return generate_non_terminator(
            eng, uniform_sample(eng, common_non_terminators));
    }

    template <typename Engine>
    NonTerminator generate_uncommon_non_terminator(Engine &eng)
    {
        return generate_non_terminator(
            eng, uniform_sample(eng, uncommon_non_terminators));
    }

    template <typename Engine>
    NonTerminator generate_dup(Engine &eng)
    {
        return generate_non_terminator(
            eng, uniform_sample(eng, dup_non_terminator));
    }

    template <typename Engine>
    Terminator generate_terminator(Engine &eng, bool const exit)
    {
        auto opcode = exit ? uniform_sample(eng, exit_terminators)
                           : uniform_sample(eng, jump_terminators);

        std::vector<std::pair<std::uint8_t, Constant>> mem_opnds;
        for (auto mem_op : memory_operands(opcode)) {
            with_probability(eng, 0.95, [&](auto &) {
                auto const safe_value = memory_constant(eng);
                mem_opnds.push_back({mem_op, safe_value});
            });
        }

        return Terminator{opcode, std::move(mem_opnds)};
    }

    template <typename Engine>
    NonTerminator generate_random_byte(Engine &eng)
    {
        auto dist = std::uniform_int_distribution<std::uint8_t>();
        return generate_non_terminator(eng, dist(eng));
    }

    template <typename Engine>
    std::vector<Instruction> generate_block(
        GeneratorFocus focus, Engine &eng, evmc_revision rev,
        std::vector<evmc::address> const &valid_addresses,
        BasicBlockInfo const &block)
    {
        static constexpr std::size_t max_block_insts = 10000;

        auto program = std::vector<Instruction>{};

        // We want a high probability of emitting a non-terminator,
        // because large basic blocks are more likely to explore
        // complex code paths in the emitter. We prefer few large
        // basic blocks over many small.
        static constexpr auto total_non_term_prob = 0.99;

        // We want push to be common, to increase probability
        // of triggering emitter optimizations.
        static constexpr auto push_weight = (37.0 / 148.0); // 25%
        // We want dup opcode to be common, because it increases
        // probability of stack elements being live, which are tricky
        // cases. Also serves as a way to avoid stack underflows.
        static constexpr auto dup_weight = (49.0 / 148.0); // 33%
        // The call weight is small, because the are all similar,
        // and they increase the number of out-of-gas errors.
        static constexpr auto call_weight = (0.03 / 148.0); // 0.02%
        static constexpr auto returndatacopy_weight = (0.03 / 148.0); // 0.02%
        static constexpr auto create_weight = (0.03 / 148.0); // 0.02%
        // The uncommon non-terminators have simple emitter
        // implementations, so we want low probability of these to
        // increase probability of the more complex code paths.
        static constexpr auto uncommon_non_term_weight = (4.5 / 148.0); // 3%
        // The common non-terminators have high probability, because
        // they have or aid with complex code paths in the emitter.
        static constexpr auto common_non_term_weight =
            1.0 -
            (push_weight + dup_weight + call_weight + returndatacopy_weight +
             create_weight + uncommon_non_term_weight);
        // 100% - 25% - 33% - 0.02% - 0.02% - 0.02% - 3% = 39.94%

        static constexpr auto push_prob = total_non_term_prob * push_weight;
        static constexpr auto dup_prob = total_non_term_prob * dup_weight;
        static constexpr auto call_prob = total_non_term_prob * call_weight;
        static constexpr auto returndatacopy_prob =
            total_non_term_prob * returndatacopy_weight;
        static constexpr auto create_prob = total_non_term_prob * create_weight;
        static constexpr auto uncommon_non_term_prob =
            total_non_term_prob * uncommon_non_term_weight;
        static constexpr auto common_non_term_prob =
            total_non_term_prob * common_non_term_weight;

        static constexpr auto random_byte_prob = 0.00001; // 1/100k
        static constexpr auto terminate_prob =
            (1 - total_non_term_prob) - random_byte_prob;

        if (block.is_jump_dest) {
            program.push_back(NonTerminator{JUMPDEST});
        }

        // With 75% probability, use 14 of the 16 available avx
        // registers immediately, to increase probability of running
        // out of avx registers.
        with_probability(eng, 0.75, [&](auto &) {
            program.push_back(NonTerminator{CALLVALUE}); // uses 1 avx register
            program.push_back(NonTerminator{GASPRICE}); // uses 1 avx register
            // Use 12 more avx registers:
            for (int i = 0; i < 12; ++i) {
                // [PREV, CALLVALUE, ...]
                program.push_back(NonTerminator{DUP2});
                // [CALLVALUE, PREV, CALLVALUE, ...]
                program.push_back(NonTerminator{DUP2});
                // [PREV, CALLVALUE, PREV, CALLVALUE, ...]
                program.push_back(NonTerminator{AND});
                // [PREV & CALLVALUE, PREV, CALLVALUE, ...]
                program.push_back(NonTerminator{SWAP1});
                // [PREV, PREV & CALLVALUE, CALLVALUE, ...]
                program.push_back(NonTerminator{SWAP2});
                // [CALLVALUE, PREV & CALLVALUE, PREV, ...]
                program.push_back(NonTerminator{SWAP1});
                // [PREV & CALLVALUE, CALLVALUE, PREV, ...]
            }
        });

        if (block.is_main) {
            // Leave a 5% chance to not generate any pushes in the main block.
            with_probability(eng, 0.95, [&](auto &g) {
                // Parameters chosen by eye:
                // - centered at around 65,
                // - roughly 10% chance of 55 or less,
                // - roughly 10% chance of 75 or more.
                auto main_pushes_dist =
                    std::binomial_distribution<std::size_t>(650, 0.1);
                auto const main_initial_pushes = main_pushes_dist(g);

                for (auto i = 0u; i < main_initial_pushes; ++i) {
                    program.push_back(generate_push(focus, g, valid_addresses));
                }
            });
        }

        for (auto terminated = false;
             !terminated && program.size() <= max_block_insts;) {
            auto next_inst = discrete_choice<Instruction>(
                eng,
                [](auto &g) { return generate_random_byte(g); },
                Choice(
                    common_non_term_prob,
                    [](auto &g) { return generate_common_non_terminator(g); }),
                Choice(
                    push_prob,
                    [focus, valid_addresses](auto &g) {
                        return generate_push(focus, g, valid_addresses);
                    }),
                Choice(dup_prob, [](auto &g) { return generate_dup(g); }),
                Choice(
                    call_prob,
                    [&](auto &g) {
                        return generate_call(g, rev, valid_addresses);
                    }),
                Choice(
                    returndatacopy_prob,
                    [](auto &g) { return generate_returndatacopy(g); }),
                Choice(
                    create_prob,
                    [&](auto &g) {
                        return generate_create(g, rev, valid_addresses);
                    }),
                Choice(
                    uncommon_non_term_prob,
                    [](auto &g) {
                        return generate_uncommon_non_terminator(g);
                    }),
                Choice(terminate_prob, [&](auto &g) {
                    return generate_terminator(g, block.is_exit);
                }));

            if (auto *term = std::get_if<Terminator>(&next_inst)) {
                terminated = true;

                auto op = term->opcode;

                if (op == JUMP || op == JUMPI) {
                    double valid_jump_prob = 0.0;
                    switch (focus) {
                    case GeneratorFocus::Generic:
                        valid_jump_prob = 0.90;
                        break;
                    case GeneratorFocus::Pow2:
                        valid_jump_prob = 1.0;
                        break;
                    case GeneratorFocus::DynJump:
                        valid_jump_prob = 0;
                        break;
                    }
                    with_probability(eng, valid_jump_prob, [&](auto &) {
                        program.push_back(ValidJumpDest{});
                    });
                }
                else if (op == RETURN || op == REVERT) {
                    with_probability(eng, 0.75, [&](auto &) {
                        program.push_back(memory_constant(eng));
                        program.push_back(memory_constant(eng));
                    });
                }
                else if (op == SELFDESTRUCT) {
                    with_probability(eng, 0.66, [&](auto &) {
                        program.push_back(ValidAddress{});
                    });
                }
            }

            program.emplace_back(std::move(next_inst));
        }

        return program;
    }

    void compile_address(
        std::vector<std::uint8_t> &program, evmc::address const &addr)
    {
        program.push_back(PUSH20);
        for (auto b : addr.bytes) {
            program.push_back(b);
        }
    }

    void compile_constant(std::vector<std::uint8_t> &program, Constant const &c)
    {
        program.push_back(PUSH32);

        auto const *bs = intx::as_bytes(c.value);
        for (auto i = 31; i >= 0; --i) {
            program.push_back(bs[i]);
        }
    }

    void compile_percent(std::vector<std::uint8_t> &program, uint8_t pct)
    {
        program.push_back(PUSH1);
        program.push_back(10);
        program.push_back(SWAP1);
        program.push_back(PUSH1);
        program.push_back(pct);
        program.push_back(MUL);
        program.push_back(DIV);
    }

    void compile_returndatacopy(
        std::vector<std::uint8_t> &program, ReturnDataCopy const &rdc)
    {

        if (!rdc.isTrivial) {
            program.push_back(RETURNDATASIZE);
            compile_percent(program, rdc.sizePct);
            program.push_back(RETURNDATASIZE);
            compile_percent(program, rdc.offsetPct);
            compile_constant(program, rdc.destOffset);
            program.push_back(RETURNDATASIZE);
        }
        program.push_back(RETURNDATACOPY);
    }

    void compile_create(std::vector<std::uint8_t> &program, Create const &c)
    {
        if (!c.isTrivial) {
            if (c.opcode == CREATE2) {
                compile_constant(program, c.salt);
            }
            // -> [salt (CREATE2)]

            compile_address(program, c.address);
            // -> [address, salt (CREATE2)]
            program.push_back(DUP1);
            // -> [address, address, salt (CREATE2)]
            program.push_back(EXTCODESIZE);
            // -> [size, address, salt (CREATE2)]
            program.push_back(DUP1);
            // -> [size, size, address, salt (CREATE2)]
            compile_constant(program, Constant{0});
            // -> [0, size, size, address, salt (CREATE2)]
            compile_constant(program, c.offset);
            // -> [dest_offset, 0, size, size, address, salt (CREATE2)]
            program.push_back(DUP5);
            // -> [address, dest_offset, 0, size, size, address, salt (CREATE2)]
            program.push_back(EXTCODECOPY);
            // -> [size, address, salt (CREATE2)]
            program.push_back(SWAP1);
            // -> [address, size, salt (CREATE2)]
            program.push_back(POP);
            // -> [size, salt (if CREATE2)]
            compile_constant(program, c.offset);
            // -> [dest_offset, size, salt (if CREATE2)]
            program.push_back(SELFBALANCE);
            compile_percent(program, c.balancePct);
            // -> [value, dest_offset, size, salt (if CREATE2)]
        }

        program.push_back(c.opcode);
    }

    void compile_call(std::vector<std::uint8_t> &program, Call const &call)
    {
        bool isTrivial = call.isTrivial;

        if (!isTrivial) {
            compile_constant(program, call.retSize);
            compile_constant(program, call.retOffset);
            compile_constant(program, call.argsSize);
            compile_constant(program, call.argsOffset);

            if (call.opcode == CALL || call.opcode == CALLCODE) {
                program.push_back(SELFBALANCE);
                compile_percent(program, call.balancePct);
            }

            compile_address(program, call.address);

            // send some percentage of available gas
            program.push_back(GAS);
            compile_percent(program, call.gasPct);
        }
        program.push_back(call.opcode);
    }

    void compile_push(
        std::vector<std::uint8_t> &program, Push const &push,
        std::vector<std::size_t> &jumpdest_patches)
    {
        std::visit(
            Cases{
                [&](ValidAddress const &va) {
                    if (va.address.has_value()) {
                        compile_address(program, va.address.value());
                    }
                    else {
                        program.push_back(ADDRESS);
                    }
                },
                [&](ValidJumpDest) {
                    jumpdest_patches.push_back(program.size());

                    program.push_back(PUSH4);
                    for (auto i = 0; i < 4; ++i) {
                        program.push_back(0xFF);
                    }
                },
                [&](Constant const &c) {
                    program.push_back(PUSH32);

                    auto const *bs = intx::as_bytes(c.value);
                    for (auto i = 31; i >= 0; --i) {
                        program.push_back(bs[i]);
                    }
                },
            },
            push);
    }

    void compile_push(std::vector<std::uint8_t> &program, Push const &push)
    {
        auto patches = std::vector<std::size_t>{};
        compile_push(program, push, patches);
        MONAD_VM_DEBUG_ASSERT(patches.empty());
    }

    void compile_block(
        std::vector<std::uint8_t> &program,
        std::vector<Instruction> const &block,
        std::vector<std::uint32_t> &valid_jumpdests,
        std::vector<std::size_t> &jumpdest_patches)
    {
        auto push_op = [&](auto op, auto const &opnds) {
            if (op == JUMPDEST) {
                valid_jumpdests.push_back(
                    static_cast<std::uint32_t>(program.size()));
            }

            for (auto [mem_op, safe_value] : opnds) {
                auto const byte_size =
                    count_significant_bytes(safe_value.value);
                MONAD_VM_DEBUG_ASSERT(byte_size <= 32);

                program.push_back(PUSH0 + static_cast<std::uint8_t>(byte_size));

                auto const *bs = intx::as_bytes(safe_value.value);
                for (auto i = 0u; i < byte_size; ++i) {
                    program.push_back(bs[byte_size - 1 - i]);
                }

                program.push_back(SWAP1 + mem_op);
                program.push_back(POP);
            }

            program.push_back(op);
        };

        for (auto const &inst : block) {
            std::visit(
                Cases{
                    [&](NonTerminator const &nt) {
                        push_op(nt.opcode, nt.opnds);
                    },
                    [&](Terminator const &t) { push_op(t.opcode, t.opnds); },
                    [&](Push const &p) {
                        compile_push(program, p, jumpdest_patches);
                    },
                    [&](Call const &c) { compile_call(program, c); },
                    [&](ReturnDataCopy const &r) {
                        compile_returndatacopy(program, r);
                    },
                    [&](Create const &c) { compile_create(program, c); },
                },
                inst);
        }
    }

    template <typename Engine>
    void patch_jumpdests(
        Engine &eng, std::vector<std::uint8_t> &program,
        std::vector<std::size_t> const &jumpdest_patches,
        std::vector<std::uint32_t> const &valid_jumpdests)
    {
        MONAD_VM_DEBUG_ASSERT(std::ranges::is_sorted(jumpdest_patches));
        MONAD_VM_DEBUG_ASSERT(std::ranges::is_sorted(valid_jumpdests));

        // The valid jumpdests and path locations in this program appear in
        // sorted order, so we can bias the generator towards "forwards" jumps
        // in the CFG by simply keeping track of a pointer to the first jumpdest
        // greater than the program offset that we're currently patching, and
        // sampling from that range with greater probability.

        auto forward_jds_begin = valid_jumpdests.begin();
        auto const forward_jds_end = valid_jumpdests.end();

        for (auto const patch : jumpdest_patches) {
            MONAD_VM_DEBUG_ASSERT(patch + 4 < program.size());
            MONAD_VM_DEBUG_ASSERT(program[patch] == PUSH4);

            forward_jds_begin = std::find_if(
                forward_jds_begin, forward_jds_end, [patch](auto jd) {
                    return jd > patch;
                });

            // If there are no possible forwards jumps (i.e. we're in the last
            // block) then we need to unconditionally sample from the full set
            // of jumpdests.
            auto const forward_prob =
                (forward_jds_begin != forward_jds_end) ? 0.9 : 0.0;

            auto const jd = discrete_choice<std::size_t>(
                eng,
                [&](auto &g) {
                    if (valid_jumpdests.size() == 0) {
                        return random_uint32(g);
                    }
                    else {
                        return uniform_sample(g, valid_jumpdests);
                    }
                },
                Choice(forward_prob, [&](auto &g) {
                    return uniform_sample(
                        g, forward_jds_begin, forward_jds_end);
                }));

            auto const *bs = intx::as_bytes(jd);
            for (auto i = 0u; i < 4; ++i) {
                auto &dest = program[patch + i + 1];
                MONAD_VM_DEBUG_ASSERT(dest == 0xFF);

                dest = bs[3 - i];
            }

            // If there is only one or zero valid jump destinations,
            // then we will likely fail due to invalid jump destination
            // or due to generating a loop. So in this case we will generate a
            // return instead of a jump(i) instruction with 90% probability.
            auto const return_prob = valid_jumpdests.size() > 1 ? 0 : 0.9;
            with_probability(eng, return_prob, [&](auto &) {
                program[patch] = PUSH1;
                program[patch + 2] = PUSH1;
                program[patch + 4] = RETURN;
            });
        }
    }

    template <typename Engine>
    std::vector<std::uint8_t> generate_program(
        GeneratorFocus focus, Engine &eng, evmc_revision rev,
        std::vector<evmc::address> const &valid_addresses)
    {
        auto prog = std::vector<std::uint8_t>{};

        auto const block_dist_p = discrete_choice<double>(
            eng,
            [](auto &) {
                // Approximately 24% probability of 5 or more basic blocks,
                // and 30% probability of just 1 basic block.
                return 0.30;
            },
            Choice(0.10, [](auto &) {
                // Approximately 50% probability of 17 or more basic blocks,
                // and 4% probability of just 1 basic block.
                return 0.04;
            }));
        auto blocks_dist = std::geometric_distribution(block_dist_p);
        auto const n_blocks = 1 + blocks_dist(eng);

        auto exit_blocks_dist = std::uniform_int_distribution(1, n_blocks);
        auto const n_exit_blocks = exit_blocks_dist(eng);

        auto blocks = std::vector<BasicBlockInfo>{};

        for (auto i = 0; i < n_blocks; ++i) {
            // main block is the first
            auto const is_main = (i == 0);
            // exit blocks are the last n_exit_blocks blocks
            auto const is_exit = (i > n_blocks - n_exit_blocks);
            // with 2/3 probability, a block is a valid jump destination
            auto const is_jump_dest = toss(eng, 0.66);

            blocks.push_back(BasicBlockInfo{is_main, is_exit, is_jump_dest});
        }

        auto valid_jumpdests = std::vector<std::uint32_t>{};
        auto jumpdest_patches = std::vector<std::size_t>{};

        for (auto const &block : blocks) {
            auto const block_instructions =
                generate_block(focus, eng, rev, valid_addresses, block);

            compile_block(
                prog, block_instructions, valid_jumpdests, jumpdest_patches);
        }

        patch_jumpdests(eng, prog, jumpdest_patches, valid_jumpdests);
        return prog;
    }

    template <typename Engine, typename LookupFunc>
    auto message_gas(
        Engine &eng, evmc::address const &target,
        std::vector<evmc::address> const &contract_addresses,
        LookupFunc address_lookup) noexcept
    {
        using gas_t = decltype(evmc_message::gas);

        auto const base_gas = discrete_choice<double>(
            eng,
            [](auto &g) {
                auto base_dist = std::normal_distribution<double>(
                    /* mean */ 1'000'000, /* stddev */ 400'000);
                return std::max(0.0, base_dist(g));
            },
            Choice(0.10, [](auto &) { return 0.0; }));

        auto const factor =
            address_lookup(target).size() * contract_addresses.size();

        auto scale_dist = std::normal_distribution(
            /* mean */ 32.0, /* stddev */ 16.0);
        auto const scale = std::max(0.0, scale_dist(eng));

        auto const gas = base_gas + static_cast<double>(factor) * scale;

        MONAD_VM_DEBUG_ASSERT(
            gas <= static_cast<double>(std::numeric_limits<gas_t>::max()));
        MONAD_VM_DEBUG_ASSERT(gas >= 0);

        return static_cast<gas_t>(gas);
    }

    struct message_deleter
    {
        static void operator()(evmc_message *msg) noexcept
        {
            if (!msg) {
                return;
            }

            delete[] msg->input_data;
            delete msg;
        }
    };

    using message_ptr = std::unique_ptr<evmc_message, message_deleter>;

    /**
     * Generates and allocates a calldata buffer containing push-like elements.
     *
     * The caller of this function is responsible for deallocating the buffer
     * appropriately (e.g. by assigning it to the `input_data` member of a
     * `message_ptr`, or explicitly via `delete[]`).
     */
    template <typename Engine>
    std::uint8_t const *generate_input_data(
        GeneratorFocus focus, Engine &eng, std::size_t const size,
        std::vector<evmc::address> const &contract_addresses)
    {
        if (size == 0) {
            return nullptr;
        }

        auto data = std::vector<std::uint8_t>();
        data.reserve(size);

        while (data.size() < size) {
            auto const next_item =
                generate_calldata_item(focus, eng, contract_addresses);
            compile_push(data, next_item);
        }

        auto *const return_buf = new std::uint8_t[size];

        MONAD_VM_DEBUG_ASSERT(data.size() >= size);
        std::copy_n(data.begin(), size, &return_buf[0]);

        return return_buf;
    }

    /**
     * Generate a random EVMC message.
     *
     * Returns a managed pointer to a message, rather than the message itself in
     * order that we can control the lifetime of the `input_data` buffer.
     *
     * Additionally, the `lookup :: Address -> Code` argument here is passed as
     * a lambda to decouple the message generator from any particular concrete
     * state representation. The fuzzer implementation is responsible for
     * instantiating this lookup as appropriate.
     */
    template <typename Engine, typename LookupFunc>
    message_ptr generate_message(
        GeneratorFocus focus, Engine &eng,
        std::vector<evmc::address> const &contract_addresses,
        std::vector<evmc::address> const &known_eoas,
        LookupFunc address_lookup) noexcept
    {
        auto const kind = uniform_sample(
            eng, std::array{EVMC_CALL, EVMC_DELEGATECALL, EVMC_CALLCODE});

        auto const static_flag = discrete_choice<evmc_flags>(
            eng,
            [](auto &) { return static_cast<evmc_flags>(0); },
            Choice(0.02, [](auto &) { return EVMC_STATIC; }));
        auto const delegated_flag = discrete_choice<evmc_flags>(
            eng,
            [](auto &) { return static_cast<evmc_flags>(0); },
            Choice(0.5, [](auto &) { return EVMC_DELEGATED; }));

        auto const flags =
            static_cast<evmc_flags>(static_flag | delegated_flag);

        auto const depth =
            std::uniform_int_distribution<decltype(evmc_message::depth)>(
                0, 1023)(eng);

        auto const target = uniform_sample(eng, contract_addresses);

        auto const recipient =
            (kind == EVMC_CALL)
                ? target
                : discrete_choice<evmc::address>(
                      eng,
                      [&](auto &g) {
                          return uniform_sample(g, contract_addresses);
                      },
                      Choice(
                          0.001, [&](auto &g) { return random_address(g); }));

        auto const eoa_prob = known_eoas.empty() ? 0.0 : 0.5;
        auto const sender = discrete_choice<evmc::address>(
            eng,
            [&](auto &g) { return uniform_sample(g, contract_addresses); },
            Choice(eoa_prob, [&](auto &g) {
                return uniform_sample(g, known_eoas);
            }));

        auto const input_size =
            std::uniform_int_distribution<std::size_t>(0, 1024)(eng);
        auto const *input_data =
            generate_input_data(focus, eng, input_size, contract_addresses);

        auto const value = discrete_choice<runtime::uint256_t>(
            eng, [](auto &) { return 0; }, Choice(0.9, [&](auto &g) {
                return random_constant<128>(g).value;
            }));

        auto const salt = random_constant(eng).value;

        auto const &code = address_lookup(target);

        return message_ptr{new evmc_message{
            .kind = kind,
            .flags = flags,
            .depth = depth,
            .gas =
                message_gas(eng, recipient, contract_addresses, address_lookup),
            .recipient = recipient,
            .sender = sender,
            .input_data = input_data,
            .input_size = input_size,
            .value = value.template store_be<evmc::bytes32>(),
            .create2_salt = salt.template store_be<evmc::bytes32>(),
            .code_address = target,
            .code = code.data(),
            .code_size = code.size(),
        }};
    }

}
