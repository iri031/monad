#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/int.hpp>

#include <ankerl/unordered_dense.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <immer/array.hpp>
#pragma GCC diagnostic pop

MONAD_NAMESPACE_BEGIN

constexpr unsigned EXECUTION_DELAY = 3;

class InflightExpensesBuffer
{
    using Expenses = ankerl::unordered_dense::segmented_map<Address, uint512_t>;
    using InflightExpenses = immer::array<Expenses>;

    ankerl::unordered_dense::segmented_map<uint64_t, InflightExpenses>
        proposals_{};
    uint64_t block_number_{0};
    uint64_t round_{0};
    uint64_t parent_round_{0};
    Expenses expenses_{};

public:
    void set(uint64_t block_number, uint64_t round, uint64_t parent_round);
    void add(Address const &, uint512_t expense);
    void propose();
    void finalize(uint64_t round);
    uint512_t sum(Address const &) const;
};

static_assert(sizeof(InflightExpensesBuffer) == 152);
static_assert(alignof(InflightExpensesBuffer) == 8);

MONAD_NAMESPACE_END
