#pragma once

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/hex_literal.hpp>
#include <category/mpt2/compute.hpp>
#include <category/mpt2/state_machine.hpp>
#include <category/mpt2/trie.hpp>
#include <category/storage/test/test_fixtures.hpp>

#include <cstdint>
#include <vector>

using namespace monad::storage_test;

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

    template <class... Updates>
    [[nodiscard]] constexpr chunk_offset_t upsert_updates(
        UpdateAux &aux, StateMachine &sm, chunk_offset_t const old_offset,
        Updates... updates)
    {
        UpdateList update_ls;
        (update_ls.push_front(updates), ...);
        return upsert(aux, sm, old_offset, std::move(update_ls));
    }

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

    struct UpdateAuxFixture : public DbStorageFixture
    {
        UpdateAux aux;
        std::unique_ptr<StateMachine> sm;

        UpdateAuxFixture()
            : DbStorageFixture()
            , aux(db_storage) // using default history
            , sm(std::make_unique<StateMachineAlwaysMerkle>())
        {
        }

        monad::byte_string root_hash(Node *const root)
        {
            if (root) {
                monad::byte_string data(32, 0);
                auto const len =
                    this->sm->get_compute().compute(data.data(), root);
                if (len < KECCAK256_SIZE) {
                    keccak256(data.data(), len, data.data());
                }
                return data;
            }
            return empty_trie_hash;
        }
    };

}
