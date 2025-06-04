#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <functional>

MONAD_NAMESPACE_BEGIN

Result<std::vector<Address>>
recover_senders(fiber::PriorityPool &priority_pool, Block const &block)
{
    std::vector<std::function<Result<Address>()>> tasks{
        block.transactions.size()};
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        tasks[i] = [&transaction = block.transactions[i]] {
            return recover_sender(transaction);
        };
    }
    return priority_pool.submit_and_map(std::span{tasks}, std::identity{});
}

MONAD_NAMESPACE_END
