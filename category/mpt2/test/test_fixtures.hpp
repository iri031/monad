#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/hex_literal.hpp>
#include <category/mpt2/compute.hpp>
#include <category/mpt2/state_machine.hpp>
#include <category/mpt2/trie.hpp>

#include <cstdint>
#include <vector>

namespace monad::trie_test
{
    using namespace MONAD_MPT2_NAMESPACE;
    using namespace monad::literals;

    namespace fixed_updates
    {
        std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
            {0x1234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex},
            {0x1234567822345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebabe_hex},
            {0x1234567832345678123456781234567812345678123456781234567812345671_hex,
             0xdeadcafedeadcafedeadcafedeadcafedeadcafedeadcafedeadcafedeadcafe_hex},
            {0x1234567832345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbabedeadbabedeadbabedeadbabedeadbabedeadbabedeadbabedeadbabe_hex}};
    };

    struct DummyComputeLeafData
    {
        // TEMPORARY for POC
        // compute leaf data as - concat(input_leaf, hash);
        static byte_string compute(Node const &node)
        {
            return byte_string{node.value()} + byte_string{node.data()};
        }
    };

    using MerkleCompute = MerkleComputeBase<DummyComputeLeafData>;

    template <class Compute>
    class StateMachineAlways final : public StateMachine
    {
    private:
        size_t depth{0};

    public:
        StateMachineAlways() = default;

        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<StateMachineAlways<Compute>>(*this);
        }

        virtual void down(unsigned char) override
        {
            ++depth;
        }

        virtual void up(size_t n) override
        {
            MONAD_DEBUG_ASSERT(n <= depth);
            depth -= n;
        }

        virtual Compute &get_compute() const override
        {
            static Compute c{};
            return c;
        }

        virtual constexpr bool compact() const override
        {
            return true;
        }
    };

    using StateMachineAlwaysMerkle = StateMachineAlways<MerkleCompute>;
}
