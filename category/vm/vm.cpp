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

#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/keccak.hpp>
// #include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/vm/code.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <memory>
#include <span>
#include <tbb/concurrent_hash_map.h>

namespace fs = std::filesystem;

namespace monad::vm
{
    using namespace monad::vm::utils;

    // Copied fmt::formatter for evmc::address from address_fmt.hpp to avoid
    // circular dependency.
    auto format_address(evmc::address const &value) {
        return fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
    }

    typedef tbb::concurrent_hash_map<evmc::address, int, tbb::tbb_hash_compare<evmc::address>> ContractTable;
    typedef ContractTable::accessor Accessor;

    ContractTable call_counter;
    const int CONTRACT_CALL_THRESHOLD = 5;

    VM::VM(
        bool enable_async, std::size_t max_stack_cache,
        std::size_t max_memory_cache)
        : compiler_{enable_async}
        , stack_allocator_{max_stack_cache}
        , memory_allocator_{max_memory_cache}
    {
    }

    evmc::Result VM::execute2(
        evmc_revision rev, evmc_host_interface const *host,
        evmc_host_context *context, evmc_message const *msg,
        evmc::bytes32 const &code_hash, SharedVarcode const &vcode)
    {
        auto const &icode = vcode->intercode();
        auto const &ncode = vcode->nativecode();
        if (MONAD_VM_LIKELY(ncode != nullptr)) {
            // The bytecode is compiled.
            if (MONAD_VM_UNLIKELY(ncode->revision() != rev)) {
                // Revision change. The bytecode was compiled pre revision
                // change, so start async compilation immediately for the new
                // revision. Execute with interpreter in the meantime.
                compiler_.async_compile(
                    rev, code_hash, icode, compiler_config_);
                return execute_intercode(rev, host, context, msg, icode);
            }
            auto const entry = ncode->entrypoint();
            if (MONAD_VM_UNLIKELY(entry == nullptr)) {
                // Compilation has failed in this revision, so just execute
                // with interpreter.
                return execute_intercode(rev, host, context, msg, icode);
            }
            // Bytecode has been successfully compiled for the right revision.
            return execute_native_entrypoint(host, context, msg, icode, entry);
        }
        if (!compiler_.is_varcode_cache_warm()) {
            // If cache is not warm then start async compilation immediately,
            // and execute with interpreter in the meantime.
            compiler_.async_compile(rev, code_hash, icode, compiler_config_);
            return execute_intercode(rev, host, context, msg, icode);
        }
        // Execute with interpreter. We will start async compilation when
        // the accumulated execution gas spent by interpreter on the bytecode
        // becomes sufficiently high.
        auto result = execute_intercode(rev, host, context, msg, icode);
        auto const bound = compiler::native::max_code_size(
            compiler_config_.max_code_size_offset, icode->code_size());
        MONAD_VM_DEBUG_ASSERT(result.gas_left >= 0);
        MONAD_VM_DEBUG_ASSERT(msg->gas >= result.gas_left);
        uint64_t const gas_used =
            static_cast<uint64_t>(msg->gas - result.gas_left);
        // Note that execution gas is counted for the second time via the
        // intercode_gas_used function if this is a re-execution.
        if (vcode->intercode_gas_used(gas_used) >= *bound) {
            compiler_.async_compile(rev, code_hash, icode, compiler_config_);
        }
        return result;
    }

    evmc::Result VM::execute(
        evmc_revision rev, evmc_host_interface const *host,
        evmc_host_context *context, evmc_message const *msg,
        evmc::bytes32 const &code_hash, SharedVarcode const &vcode)
    {
        auto result = execute2(rev, host, context, msg, code_hash, vcode);

        if (result.status_code == EVMC_SUCCESS) {
            ContractTable::accessor accessor;
            const auto itemIsNew = call_counter.insert(accessor, msg->code_address);
            if (itemIsNew) {
                accessor->second = 1;
            }
            else {
                const int call_count = accessor->second;
                if (call_count != -1) {
                    if (call_count > CONTRACT_CALL_THRESHOLD) {

                        // mark for insertion into the contracts dump
                        accessor->second = -1;
                        auto contracts_dir_var = std::getenv("CONTRACTS_DIR");
                        MONAD_ASSERT(contracts_dir_var);

                        // content addressable path for the contract using keccak of the actual code
                        auto const code_buf = vcode->intercode().get()->code();
                        auto const code_len = *(vcode->intercode().get()->code_size());
                        auto const code_hash = keccak256(code_buf);

                        auto code_hash_dir = fs::path(contracts_dir_var) / "code_hash";
                        fs::create_directories(code_hash_dir);

                        auto contract_path = code_hash_dir / fmt::format("{}", intx::hex(intx::be::load<intx::uint256>(code_hash.bytes)));

                        auto os = std::ofstream(contract_path);
                        os.write(
                            reinterpret_cast<char const *>(code_buf),
                            static_cast<std::streamsize>(code_len));

                        auto block_id = host->get_tx_context(context).block_number;
                        auto block_prefix =
                            fmt::format("{}M", block_id / 1'000'000);

                        auto code_address_dir = fs::path(contracts_dir_var) / "code_address" / block_prefix /
                                fmt::format("{:02x}", msg->code_address.bytes[0]) /
                                fmt::format("{:02x}", msg->code_address.bytes[1]);

                        fs::create_directories(code_address_dir);

                        const evmc::address& addr = msg->code_address;
                        auto contract_address_path = code_address_dir / format_address(addr);

                        fs::create_symlink(contract_path, contract_address_path);
                    }
                    else {
                        accessor->second = call_count + 1;
                    }
                }
            }
            accessor.release();
        }

        return result;
    }

    evmc::Result VM::execute_raw(
        evmc_revision rev, evmc_host_interface const *host,
        evmc_host_context *context, evmc_message const *msg,
        std::span<uint8_t const> code)
    {
        stats_.event_execute_raw();
        auto const stack_ptr = stack_allocator_.allocate();
        auto ctx =
            runtime::Context::from(memory_allocator_, host, context, msg, code);

        interpreter::execute(rev, ctx, Intercode{code}, stack_ptr.get());

        return ctx.copy_to_evmc_result();
    }

    evmc::Result VM::execute_intercode(
        evmc_revision rev, evmc_host_interface const *host,
        evmc_host_context *context, evmc_message const *msg,
        SharedIntercode const &icode)
    {
        stats_.event_execute_intercode();
        uint8_t const *const code = icode->code();
        size_t const code_size = icode->size();
        auto const stack_ptr = stack_allocator_.allocate();
        auto ctx = runtime::Context::from(
            memory_allocator_, host, context, msg, {code, code_size});

        interpreter::execute(rev, ctx, *icode, stack_ptr.get());

        return ctx.copy_to_evmc_result();
    }

    evmc::Result VM::execute_native_entrypoint(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_message const *msg, SharedIntercode const &icode,
        compiler::native::entrypoint_t entry)
    {
        stats_.event_execute_native_entrypoint();
        uint8_t const *const code = icode->code();
        size_t const code_size = icode->size();
        auto ctx = runtime::Context::from(
            memory_allocator_, host, context, msg, {code, code_size});

        auto const stack_ptr = stack_allocator_.allocate();

        entry(&ctx, stack_ptr.get());

        return ctx.copy_to_evmc_result();
    }
}
