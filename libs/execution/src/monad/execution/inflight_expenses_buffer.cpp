#include <monad/config.hpp>
#include <monad/execution/inflight_expenses_buffer.hpp>

MONAD_NAMESPACE_BEGIN

void InflightExpensesBuffer::set(
    uint64_t const block_number, uint64_t const round,
    uint64_t const parent_round)
{
    MONAD_ASSERT(expenses_.empty());
    block_number_ = block_number;
    round_ = round;
    parent_round_ = parent_round;
}

void InflightExpensesBuffer::add(Address const &a, uint512_t const expense)
{
    expenses_[a] += expense;
}

void InflightExpensesBuffer::propose()
{
    InflightExpenses const &parent = proposals_.contains(parent_round_)
                                         ? proposals_.at(parent_round_)
                                         : InflightExpenses{EXECUTION_DELAY};
    MONAD_ASSERT(
        proposals_
            .emplace(
                round_,
                parent.set(
                    block_number_ % EXECUTION_DELAY, std::move(expenses_)))
            .second);
    expenses_.clear();
}

void InflightExpensesBuffer::finalize(uint64_t const round)
{
    std::erase_if(
        proposals_, [round](auto const &it) { return it.first < round; });
}

uint512_t InflightExpensesBuffer::sum(Address const &a) const
{
    MONAD_ASSERT(proposals_.contains(round_));
    uint512_t sum = 0;
    for (auto const &m : proposals_.at(round_)) {
        if (m.contains(a)) {
            sum += m.at(a);
        }
    }
    return sum;
}

MONAD_NAMESPACE_END
