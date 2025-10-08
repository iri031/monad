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

#include "assertions.hpp"
#include "block.hpp"
#include "compiler_hook.hpp"
#include "test_vm.hpp"

#include "account.hpp"
#include "hash_utils.hpp"
#include "host.hpp"
#include "state.hpp"
#include "test_state.hpp"
#include "transaction.hpp"

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
#include <category/vm/fuzzing/generator/shrinker.hpp>
#include <category/vm/utils/debug.hpp>

#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>

#include <evmone/constants.hpp>
#include <evmone/evmone.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <CLI/CLI.hpp>
#include <intx/intx.hpp>

#include <algorithm>
#include <array>
#include <bits/chrono.h>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <span>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace evmone::state;
using namespace evmc::literals;
using namespace monad;
using namespace monad::vm::fuzzing;
using namespace std::chrono_literals;

using enum monad::vm::compiler::EvmOpCode;

static constexpr std::string_view to_string(evmc_status_code const sc) noexcept
{
    switch (sc) {
    case EVMC_SUCCESS:
        return "SUCCESS";
    case EVMC_FAILURE:
        return "FAILURE";
    case EVMC_REVERT:
        return "REVERT";
    case EVMC_OUT_OF_GAS:
        return "OUT_OF_GAS";
    case EVMC_INVALID_INSTRUCTION:
        return "INVALID_INSTRUCTION";
    case EVMC_UNDEFINED_INSTRUCTION:
        return "UNDEFINED_INSTRUCTION";
    case EVMC_STACK_OVERFLOW:
        return "STACK_OVERFLOW";
    case EVMC_STACK_UNDERFLOW:
        return "STACK_UNDERFLOW";
    case EVMC_BAD_JUMP_DESTINATION:
        return "BAD_JUMP_DESTINATION";
    case EVMC_INVALID_MEMORY_ACCESS:
        return "INVALID_MEMORY_ACCESS";
    case EVMC_CALL_DEPTH_EXCEEDED:
        return "CALL_DEPTH_EXCEEDED";
    case EVMC_STATIC_MODE_VIOLATION:
        return "STATIC_MODE_VIOLATION";
    case EVMC_PRECOMPILE_FAILURE:
        return "PRECOMPILE_FAILURE";
    case EVMC_ARGUMENT_OUT_OF_RANGE:
        return "ARGUMENT_OUT_OF_RANGE";
    case EVMC_INSUFFICIENT_BALANCE:
        return "INSUFFICIENT_BALANCE";
    case EVMC_INTERNAL_ERROR:
        return "INTERNAL_ERROR";
    case EVMC_REJECTED:
        return "REJECTED";
    case EVMC_OUT_OF_MEMORY:
        return "OUT_OF_MEMORY";
    default:
        return "OTHER";
    }
}

static constexpr auto genesis_address =
    0xBEEFCAFE000000000000000000000000BA5EBA11_address;

static constexpr auto block_gas_limit = 300'000'000;

static evmone::test::TestState initial_state()
{
    auto init = evmone::test::TestState{};
    // Genesis account with some large balance, but sufficiently small
    // so that token supply will not overflow uint256.
    init[genesis_address] = {
        .balance = std::numeric_limits<intx::uint256>::max() / 2,
        .storage = {},
        .code = {}};
    return init;
}

static Transaction tx_from(State &state, evmc::address const &addr) noexcept
{
    auto tx = Transaction{};
    tx.gas_limit = block_gas_limit;
    tx.sender = addr;
    tx.nonce = state.get_or_insert(addr).nonce;
    return tx;
}

// Derived from the evmone transition implementation; transaction-related
// book-keeping is elided here to keep the implementation simple and allow us to
// send arbitrary messages to update the state.
static evmc::Result transition(
    State &state, evmc_message const &msg, evmc_revision const rev,
    evmc::VM &vm, std::int64_t const block_gas_left)
{
    // Pre-transaction clean-up.
    // - Clear transient storage.
    // - Set accounts and their storage access status to cold.
    // - Clear the "just created" account flag.
    for (auto &[addr, acc] : state.get_modified_accounts()) {
        acc.transient_storage.clear();
        acc.access_status = EVMC_ACCESS_COLD;
        acc.just_created = false;
        for (auto &[key, val] : acc.storage) {
            val.access_status = EVMC_ACCESS_COLD;
            val.original = val.current;
        }
    }

    // TODO(BSC): fill out block and host context properly; should all work fine
    // for the moment as zero values from the perspective of the VM
    // implementations.
    auto block = BlockInfo{};
    auto hashes = evmone::test::TestBlockHashes{};
    auto tx = tx_from(state, msg.sender);
    tx.to = msg.recipient;

    constexpr auto effective_gas_price = 10;

    auto *sender_ptr = state.find(msg.sender);
    auto &sender_acc =
        (sender_ptr != nullptr) ? *sender_ptr : state.insert(msg.sender);

    ++sender_acc.nonce;
    sender_acc.balance -= block_gas_left * effective_gas_price;

    Host host{rev, vm, state, block, hashes, tx};

    sender_acc.access_status = EVMC_ACCESS_WARM; // Tx sender is always warm.
    if (tx.to.has_value()) {
        host.access_account(*tx.to);
    }

    auto result = host.call(msg);
    auto gas_used = block_gas_left - result.gas_left;

    auto const max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
    auto const refund_limit = gas_used / max_refund_quotient;
    auto const refund = std::min(result.gas_refund, refund_limit);
    gas_used -= refund;

    sender_acc.balance += (block_gas_left - gas_used) * effective_gas_price;

    // Apply destructs.
    std::erase_if(
        state.get_modified_accounts(),
        [](std::pair<address const, Account> const &p) noexcept {
            return p.second.destructed;
        });

    // Delete empty accounts after every transaction. This is strictly required
    // until Byzantium where intermediate state root hashes are part of the
    // transaction receipt.
    // TODO: Consider limiting this only to Spurious Dragon.
    if (rev >= EVMC_SPURIOUS_DRAGON) {
        std::erase_if(
            state.get_modified_accounts(),
            [](std::pair<address const, Account> const &p) noexcept {
                auto const &acc = p.second;
                return acc.erase_if_empty && acc.is_empty();
            });
    }

    return result;
}

static void deploy_contract(
    State &state, evmc::address const &to,
    std::span<std::uint8_t const> const code_)
{
    auto code = bytes{code_.data(), code_.size()};

    MONAD_VM_DEBUG_ASSERT(state.find(to) == nullptr);

    state.insert(
        to,
        Account{
            .nonce = 0,
            .balance = 0,
            .code_hash = evmone::keccak256(code),
            .storage = {},
            .transient_storage = {},
            .code = code});

    FUZZER_ASSERT(state.find(to) != nullptr);
}

static void deploy_delegated_contract(
    State &state, evmc::address const &to, evmc::address const &delegatee)
{
    std::vector<uint8_t> code = {0xef, 0x01, 0x00};
    code.append_range(delegatee.bytes);
    FUZZER_ASSERT(code.size() == 23);
    deploy_contract(state, to, code);
}

static void deploy_delegated_contracts(
    State &evmone_state, State &monad_state, evmc::address const &to,
    evmc::address delegatee)
{
    deploy_delegated_contract(evmone_state, to, delegatee);
    deploy_delegated_contract(monad_state, to, delegatee);
    assert_equal(evmone_state, monad_state);
}

// It's possible for the compiler and evmone to reach equivalent-but-not-equal
// states after both executing. For example, the compiler may exit a block
// containing an SSTORE early because of unconditional underflow later in the
// block. Evmone will instead execute the SSTORE, then roll back the change.
// Because of how rollback is implemented, this produces a state with a mapping
// `K |-> 0` for some key `K`. This won't directly compare equal to the _empty_
// state that the compiler has, and so we need to normalise the states after
// execution to remove cold zero slots.
static void clean_storage(State &state)
{
    for (auto &[addr, acc] : state.get_modified_accounts()) {
        for (auto it = acc.storage.begin(); it != acc.storage.end();) {
            auto const &[k, v] = *it;

            if (v.current == evmc::bytes32{} && v.original == evmc::bytes32{} &&
                v.access_status == EVMC_ACCESS_COLD) {
                it = acc.storage.erase(it);
            }
            else {
                ++it;
            }
        }
        for (auto it = acc.transient_storage.begin();
             it != acc.transient_storage.end();) {
            auto const &[k, v] = *it;
            if (v == evmc::bytes32{}) {
                it = acc.transient_storage.erase(it);
            }
            else {
                ++it;
            }
        }
    }
}

using random_engine_t = std::mt19937_64;

namespace
{
    struct arguments
    {
        using seed_t = random_engine_t::result_type;
        static constexpr seed_t default_seed =
            std::numeric_limits<seed_t>::max();

        std::int64_t iterations_per_run = 100;
        std::size_t messages = 4;
        seed_t seed = default_seed;
        std::size_t runs = std::numeric_limits<std::size_t>::max();
        bool print_stats = false;
        BlockchainTestVM::Implementation implementation =
            BlockchainTestVM::Implementation::Compiler;
        evmc_revision revision = EVMC_PRAGUE;
        // Disable compiler hook introducing randomness in compilation
        bool deterministic_compilation = false;

        void set_random_seed_if_default()
        {
            if (seed == default_seed) {
                seed = std::random_device()();
            }
        }
    };
}

static arguments parse_args(int const argc, char **const argv)
{
    auto app = CLI::App("Monad VM Fuzzer");
    auto args = arguments{};

    app.add_option(
        "-i,--iterations-per-run",
        args.iterations_per_run,
        "Number of fuzz iterations in each run (default 100)");

    app.add_option(
        "-n,--messages",
        args.messages,
        "Number of messages to send per iteration (default 4)");

    app.add_option(
        "--seed",
        args.seed,
        "Seed to use for reproducible fuzzing (random by default)");

    auto const impl_map =
        std::map<std::string, BlockchainTestVM::Implementation>{
            {"interpreter", BlockchainTestVM::Implementation::Interpreter},
            {"compiler", BlockchainTestVM::Implementation::Compiler},
            {"llvm", BlockchainTestVM::Implementation::LLVM},
        };

    app.add_option(
           "--implementation", args.implementation, "VM implementation to fuzz")
        ->transform(CLI::CheckedTransformer(impl_map, CLI::ignore_case));

    app.add_option(
        "-r,--runs",
        args.runs,
        "Number of runs (evm state is reset between runs) (unbounded by "
        "default)");

    app.add_flag(
        "--print-stats",
        args.print_stats,
        "Print message result statistics when logging");

    app.add_flag(
        "--deterministic-compilation",
        args.deterministic_compilation,
        "Enable deterministic compilation (no randomness)");

    auto const rev_map = std::map<std::string, evmc_revision>{
        {"FRONTIER", EVMC_FRONTIER},
        {"HOMESTEAD", EVMC_HOMESTEAD},
        {"TANGERINE_WHISTLE", EVMC_TANGERINE_WHISTLE},
        {"TANGERINE WHISTLE", EVMC_TANGERINE_WHISTLE},
        {"SPURIOUS_DRAGON", EVMC_SPURIOUS_DRAGON},
        {"SPURIOUS DRAGON", EVMC_SPURIOUS_DRAGON},
        {"BYZANTIUM", EVMC_BYZANTIUM},
        {"CONSTANTINOPLE", EVMC_CONSTANTINOPLE},
        {"PETERSBURG", EVMC_PETERSBURG},
        {"ISTANBUL", EVMC_ISTANBUL},
        {"BERLIN", EVMC_BERLIN},
        {"LONDON", EVMC_LONDON},
        {"PARIS", EVMC_PARIS},
        {"SHANGHAI", EVMC_SHANGHAI},
        {"CANCUN", EVMC_CANCUN},
        {"PRAGUE", EVMC_PRAGUE},
        {"OSAKA", EVMC_OSAKA},
        {"LATEST", EVMC_LATEST_STABLE_REVISION}};
    app.add_option(
           "--revision",
           args.revision,
           std::format(
               "Set EVM revision (default: {})",
               evmc_revision_to_string(args.revision)))
        ->transform(CLI::CheckedTransformer(rev_map, CLI::ignore_case))
        ->option_text("TEXT");

    try {
        app.parse(argc, argv);
    }
    catch (CLI::ParseError const &e) {
        std::exit(app.exit(e));
    }

    args.set_random_seed_if_default();
    return args;
}

static evmc_status_code fuzz_iteration(
    evmc_message const &msg, evmc_revision const rev, State &evmone_state,
    evmc::VM &evmone_vm, State &monad_state, evmc::VM &monad_vm,
    BlockchainTestVM::Implementation const impl)
{
    for (State &state : {std::ref(evmone_state), std::ref(monad_state)}) {
        state.get_or_insert(msg.sender);
        state.get_or_insert(msg.recipient);
    }

    auto const evmone_checkpoint = evmone_state.checkpoint();
    auto const evmone_result =
        transition(evmone_state, msg, rev, evmone_vm, block_gas_limit);

    auto const monad_checkpoint = monad_state.checkpoint();
    auto const monad_result =
        transition(monad_state, msg, rev, monad_vm, block_gas_limit);

    assert_equal(
        evmone_result,
        monad_result,
        impl == BlockchainTestVM::Implementation::Interpreter);

    if (evmone_result.status_code != EVMC_SUCCESS) {
        evmone_state.rollback(evmone_checkpoint);
    }
    clean_storage(evmone_state);

    if (monad_result.status_code != EVMC_SUCCESS) {
        monad_state.rollback(monad_checkpoint);
    }
    clean_storage(monad_state);

    assert_equal(evmone_state, monad_state);
    return evmone_result.status_code;
}

static void
log(std::chrono::high_resolution_clock::time_point start, arguments const &args,
    std::unordered_map<evmc_status_code, std::size_t> const &exit_code_stats,
    std::size_t const run_index, std::size_t const iteration_count,
    std::size_t const total_messages)
{
    using namespace std::chrono;

    constexpr auto ns_factor = duration_cast<nanoseconds>(1s).count();

    auto const end = high_resolution_clock::now();
    auto const diff = (end - start).count();
    auto const per_contract = diff / static_cast<int64_t>(iteration_count);

    std::cerr << std::format(
        "[{}]: {:.4f}s / iteration\n",
        run_index + 1,
        static_cast<double>(per_contract) / ns_factor);

    if (args.print_stats) {
        for (auto const &[k, v] : exit_code_stats) {
            auto const percentage =
                (static_cast<double>(v) / static_cast<double>(total_messages)) *
                100;
            std::cerr << std::format(
                "  {:<21}: {:.2f}%\n", to_string(k), percentage);
        }
    }
}

template <typename Engine>
static evmc::VM create_monad_vm(arguments const &args, Engine &engine)
{
    using enum BlockchainTestVM::Implementation;

    monad::vm::compiler::native::EmitterHook hook = nullptr;

    if (args.implementation == Compiler && !args.deterministic_compilation) {
        hook = compiler_emit_hook(engine);
    }

    if (args.implementation == LLVM) {
        init_llvm();
    }

    return evmc::VM(new BlockchainTestVM(args.implementation, hook));
}

// Coin toss, biased whenever p != 0.5
template <typename Engine>
static bool toss(Engine &engine, double p)
{
    std::bernoulli_distribution dist(p);
    return dist(engine);
}

struct PrecompileContract
{
    evmc::address contract_address;
    evmc::address precompile_address;
};

struct Iteration
{
    // Each iteration deploys a contract and then sends N messages to it.
    std::vector<BasicBlock> contract;
    evmc::address contract_address;
    std::optional<PrecompileContract> precompile;
    std::optional<evmc::address> delegated_contract_address;
    std::vector<evmc_message> messages;
};

struct Run
{
    std::vector<Iteration> iterations;
};

static evmc::address prepare_address(evmc::address const &from, uint64_t &nonce)
{
    return compute_create_address(from, nonce++);
}

template <typename Engine>
static Iteration prepare_iteration(
    arguments const &args, Engine &engine,
    std::vector<evmc::address> &known_addresses,
    std::vector<evmc::address> &contract_addresses,
    std::unordered_map<address, std::vector<std::uint8_t>> &contract_codes,
    uint64_t &nonce)
{
    auto const rev = args.revision;

    auto focus = discrete_choice<GeneratorFocus>(
        engine,
        [](auto &) { return GeneratorFocus::Generic; },
        Choice(0.60, [](auto &) { return GeneratorFocus::Pow2; }),
        Choice(0.05, [](auto &) { return GeneratorFocus::DynJump; }));

    std::optional<PrecompileContract> precompile = std::nullopt;
    if (rev >= EVMC_PRAGUE && toss(engine, 0.001)) {
        auto precompile_address =
            monad::vm::fuzzing::generate_precompile_address(engine, rev);
        auto const contract_address = prepare_address(genesis_address, nonce);
        known_addresses.push_back(contract_address);
        precompile = PrecompileContract{contract_address, precompile_address};
    }

    std::vector<BasicBlock> contract;
    evmc::address contract_address;
    std::optional<evmc::address> delegated_contract_address = std::nullopt;
    for (;;) {
        contract = monad::vm::fuzzing::generate_basic_blocks(
            focus, engine, rev, known_addresses);

        auto const compiled_contract = compile_program(contract);
        if (compiled_contract.size() > evmone::MAX_CODE_SIZE) {
            // The evmone host will fail when we attempt to deploy
            // contracts of this size. It rarely happens that we
            // generate contract this large.
            std::cerr << "Skipping contract of size: "
                      << compiled_contract.size() << " bytes" << std::endl;
            continue;
        }

        contract_address = prepare_address(genesis_address, nonce);

        known_addresses.push_back(contract_address);
        contract_addresses.push_back(contract_address);
        contract_codes[contract_address] = compiled_contract;

        if (args.revision >= EVMC_PRAGUE && toss(engine, 0.2)) {
            delegated_contract_address =
                prepare_address(genesis_address, nonce);
            known_addresses.push_back(*delegated_contract_address);
        }
        break;
    }

    std::vector<evmc_message> messages;
    for (auto j = 0u; j < args.messages; ++j) {
        auto msg = monad::vm::fuzzing::generate_message(
            focus,
            engine,
            contract_addresses,
            {genesis_address},
            [&](auto const &address) {
                if (auto it = contract_codes.find(address);
                    it != contract_codes.end()) {
                    return bytes{it->second.data(), it->second.size()};
                }
                return evmc::bytes{};
            });
        messages.push_back(msg);
    }
    return Iteration{
        contract,
        contract_address,
        precompile,
        delegated_contract_address,
        messages};
}

static Run prepare_run(arguments const &args)
{
    auto engine = random_engine_t(args.seed);
    auto run = Run{};
    auto contract_addresses = std::vector<evmc::address>{};
    auto known_addresses = std::vector<evmc::address>{};
    std::unordered_map<address, std::vector<std::uint8_t>> contract_codes;
    uint64_t nonce = 0;
    for (auto i = 0; i < args.iterations_per_run; ++i) {
        run.iterations.push_back(prepare_iteration(
            args,
            engine,
            known_addresses,
            contract_addresses,
            contract_codes,
            nonce));
    }
    return run;
}

static void do_run(
    std::size_t const run_index, arguments const &args, Run const &run,
    size_t &iteration_index, size_t &message_index)
{
    auto const rev = args.revision;

    auto engine = random_engine_t(args.seed);

    auto evmone_vm = evmc::VM(evmc_create_evmone());
    // Of all the source of randomness, this is the only one that can't easily
    // be pre-generated like the rest of the fuzzer input. The BlockchainTestVM
    // could be extended to signal the beginning of a compilation, allowing
    // us to reset the seed of the compiler hook to a known value, but since we
    // don't have a clear mechanism to debug the counter-examples that depend
    // on the compiler hook randomness, we ignore this for now.
    // Anyway, when shrinking, the compiler hook is disabled to make the
    // shrink predicate deterministic.
    auto monad_vm = create_monad_vm(args, engine);

    auto initial_state_ = initial_state();

    auto evmone_state = State{initial_state_};
    auto monad_state = State{initial_state_};

    auto exit_code_stats = std::unordered_map<evmc_status_code, std::size_t>{};
    auto total_messages = std::size_t{0};

    auto start_time = std::chrono::high_resolution_clock::now();

    iteration_index = 0;
    for (auto const &iteration : run.iterations) {
        if (iteration.precompile.has_value()) {
            deploy_delegated_contracts(
                evmone_state,
                monad_state,
                iteration.precompile->contract_address,
                iteration.precompile->precompile_address);
        }

        auto const &contract = compile_program(iteration.contract);

        deploy_contract(evmone_state, iteration.contract_address, contract);
        deploy_contract(monad_state, iteration.contract_address, contract);

        assert_equal(evmone_state, monad_state);

        if (iteration.delegated_contract_address.has_value()) {
            deploy_delegated_contracts(
                evmone_state,
                monad_state,
                *iteration.delegated_contract_address,
                iteration.contract_address);
        }

        message_index = 0;
        for (auto const &msg : iteration.messages) {
            ++total_messages;

            auto const ec = fuzz_iteration(
                msg,
                rev,
                evmone_state,
                evmone_vm,
                monad_state,
                monad_vm,
                args.implementation);
            ++exit_code_stats[ec];
            ++message_index;
        }
        ++iteration_index;
    }

    log(start_time,
        args,
        exit_code_stats,
        run_index,
        iteration_index,
        total_messages);
}

static bool try_run(
    std::size_t const run_index, arguments const &args, Run const &run,
    size_t &iteration_index, size_t &message_index)
{
    try {
        do_run(run_index, args, run, iteration_index, message_index);
        return true;
    }
    catch (FuzzerAssertFailure const &ex) {
        return false;
    }
}

void print_message(evmc_message const &msg)
{
    static auto kind_map = std::map<evmc_call_kind, std::string>{
        {EVMC_CALL, "CALL"},
        {EVMC_CALLCODE, "CALLCODE"},
        {EVMC_DELEGATECALL, "DELEGATECALL"},
        {EVMC_CREATE, "CREATE"},
        {EVMC_CREATE2, "CREATE2"},
        {EVMC_EOFCREATE, "EVMC_EOFCREATE"},
    };

    std::cerr << fmt::format(
        "  kind {}, gas {}, value {}\n",
        kind_map[msg.kind],
        msg.gas,
        intx::hex(intx::be::load<intx::uint256>(msg.value)));

    std::cerr << fmt::format(
        "  code_address {}, sender {}, recipient {}\n",
        address(msg.code_address),
        address(msg.sender),
        address(msg.recipient));

    std::cerr << "  input_data [" << msg.input_size << " bytes]: ";
    for (size_t i = 0; i < msg.input_size; ++i) {
        std::cerr << fmt::format("{:02x}", msg.input_data[i]);
    }
    std::cerr << "\n";
}

void print_run(Run const &run)
{
    std::cerr << "Run with " << run.iterations.size() << " iterations\n";
    for (size_t i = 0; i < run.iterations.size(); ++i) {
        auto const &it = run.iterations[i];
        auto const program = compile_program(it.contract);

        auto const code_hash = evmone::keccak256(to_byte_string_view(program));
        auto const code_hash_str =
            intx::hex(intx::be::load<intx::uint256>(code_hash.bytes));
        std::cerr << fmt::format(
            "Iteration {}: contract (hash {}) at address {} (size: {} "
            "bytes):\n",
            i,
            code_hash_str,
            it.contract_address,
            program.size());

        auto const &ir = monad::vm::compiler::basic_blocks::unsafe_make_ir<
            EvmTraits<EVMC_LATEST_STABLE_REVISION>>(program);
        for (auto const &block : ir.blocks()) {
            std::cerr << std::format("{}", block) << "\n";
        }

        for (size_t j = 0; j < it.messages.size(); ++j) {
            auto const &msg = it.messages[j];
            std::cerr << fmt::format("Message[{}]:\n", j);
            print_message(msg);
        }
    }
}

static bool try_singleton_run(
    std::size_t const run_index, arguments const &args,
    std::vector<BasicBlock> contract, evmc::address contract_address,
    evmc_message failed_message)
{
    auto run = Run{};
    run.iterations = {Iteration{
        .contract = contract,
        .contract_address = contract_address,
        .precompile = std::nullopt,
        .delegated_contract_address = std::nullopt,
        .messages = {failed_message}}};
    size_t iteration_index = 0;
    size_t message_index = 0;
    return try_run(run_index, args, run, iteration_index, message_index);
}

// A singleton run is one with a single contract and a single message.
static Run shrink_singleton_run(
    std::size_t const run_index, arguments const &args,
    std::vector<BasicBlock> original_contract, evmc::address contract_address,
    evmc_message failed_message)
{
    auto engine = random_engine_t(args.seed);
    int iteration_count = 0;
    auto contract = original_contract;

    while (++iteration_count < 100) { // After 100 shrinker failure, give up.
        if (contract.size() == 0) {
            break; // Nothing to shrink
        }

        auto [new_contract, removed_block_ix] =
            shrink_contract(engine, contract);

        if (!try_singleton_run(
                run_index,
                args,
                new_contract,
                contract_address,
                failed_message)) {
            // Block was not needed
            contract = std::move(new_contract);
            iteration_count = 0;
            continue;
        }
        else if (contract[removed_block_ix].instructions.size() > 0) {
            // Try to remove instructions from the block instead
            // First try with ranges of instructions
            auto new_contract2 =
                shrink_block(engine, contract, removed_block_ix);
            if (!try_singleton_run(
                    run_index,
                    args,
                    new_contract2,
                    contract_address,
                    failed_message)) {
                contract = std::move(new_contract2);
                iteration_count = 0;
                continue;
            }
            else {
                // Idea: Replace instructions with simpler/shorter instructions?
            }
        }
        else {
            // Block is empty but cannot be removed. This can only happen if
            // the block is a JUMPDEST and the next block is not a JUMPDEST
            // and depends on the fallthrough from the JUMPDEST block.
            auto [new_contract, shrunk_contract] =
                propagate_jumpdest(contract, removed_block_ix);
            if (shrunk_contract && !try_singleton_run(
                                       run_index,
                                       args,
                                       new_contract,
                                       contract_address,
                                       failed_message)) {
                contract = std::move(new_contract);
                iteration_count = 0;
            }
        }
    }

    // Make sure the final shrunken contract still fails
    FUZZER_ASSERT(!try_singleton_run(
        run_index, args, contract, contract_address, failed_message));

    return Run{
        .iterations = {Iteration{
            .contract = contract,
            .contract_address = contract_address,
            .precompile = std::nullopt,
            .delegated_contract_address = std::nullopt,
            .messages = {failed_message}}}};
}

static Run shrink_run(
    std::size_t const run_index, arguments const &args, Run const &run,
    size_t failed_iteration_index, size_t failed_message_index)
{
    // Assume that the contract that failed didn't depend on any of the previous
    // contracts. This is not always true, but most counter-examples are of this
    // form.
    // Prepare a run with only the msg.recipient contract and the message that
    // caused the failure.
    auto contract_map =
        std::unordered_map<evmc::address, std::vector<BasicBlock>>{};
    for (auto const &it : run.iterations) {
        contract_map.insert({it.contract_address, it.contract});
    }

    auto const &failed_iteration = run.iterations[failed_iteration_index];
    auto const &failed_message =
        failed_iteration.messages[failed_message_index];
    auto const &failed_contract_it =
        contract_map.find(failed_message.code_address);
    if (failed_contract_it == contract_map.end()) {
        std::cerr << "Failed to find contract that caused the failure\n";
        return run;
    }
    auto const &failed_contract = failed_contract_it->second;

    if (try_singleton_run(
            run_index,
            args,
            failed_contract,
            failed_message.code_address,
            failed_message)) {
        std::cerr << "Shrinker: Contract depends on other contracts or state, "
                     "cannot shrink.\n";
        /*
            To shrink the entire run, we'd need to find which of the previous
            contracts/messages the failed contract execution depends on. A
            solution could be to trace the execution of the failing run, and log
            which accounts/storage slots were accessed during the execution of
            the failing contract, retry with those contracts, and repeat until
            we reach a fixed point before starting to shrink the contracts.

            This is likely too complicated and not that effective comparing to
            simply deleting contracts/messages from the run and seeing if the
            failure still happens. To speed up the process, we can truncate
            the tail of the run first (after the failing contract/message), then
            reorder a few contracts and messages and try again.
        */
        return run;
    }
    else {
        return shrink_singleton_run(
            run_index,
            args,
            failed_contract,
            failed_message.code_address,
            failed_message);
    }
}

static void run_loop(int argc, char **argv)
{
    auto args = parse_args(argc, argv);
    auto const *msg_rev = evmc_revision_to_string(args.revision);
    for (auto i = 0u; i < args.runs; ++i) {
        std::cerr << std::format(
            "Fuzzing with seed @ {}: {}\n", msg_rev, args.seed);

        auto const &run = prepare_run(args);
        size_t iteration_index = 0;
        size_t message_index = 0;
        try {
            do_run(i, args, run, iteration_index, message_index);
        }
        catch (FuzzerAssertFailure const &ex) {
            // Disable randomness in compilation for shrinking
            args.deterministic_compilation = true;
            auto const &shrunk_run =
                shrink_run(i + 1, args, run, iteration_index, message_index);
            std::cerr << "Original counter-example found by fuzzer:\n";
            print_run(run);
            std::cerr << "Shrunk counter-example found by fuzzer:\n";
            print_run(shrunk_run);
            std::exit(1);
        }
        args.seed = random_engine_t(args.seed)();
    }
}

int main(int argc, char **argv)
{
    if (monad::vm::utils::is_fuzzing_monad_vm) {
        run_loop(argc, argv);
        return 0;
    }
    std::cerr << "\nFuzzer not started:\n"
                 "Make sure to configure with -DMONAD_COMPILER_TESTING=ON and\n"
                 "set environment variable MONAD_COMPILER_FUZZING=1 before\n"
                 "starting the fuzzer\n";
    return 1;
}
