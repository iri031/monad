#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/fee_buffer.hpp>

#include <functional>
#include <vector>

MONAD_NAMESPACE_BEGIN

void FeeBuffer::set(
    uint64_t const block_number, bytes32_t const &id,
    bytes32_t const &parent_id)
{
    MONAD_ASSERT(fees_.empty());
    block_number_ = block_number;
    id_ = id;
    parent_id_ = parent_id;
}

void FeeBuffer::note(uint64_t const i, Address const &a, uint512_t const fee)
{
    MONAD_ASSERT(fees_[a].empty() || fees_[a].back().first < i);
    fees_[a].emplace_back(i, fee);
}

void FeeBuffer::propose()
{
    ProposalFees const &parent = proposals_.contains(parent_id_)
                                     ? proposals_.at(parent_id_).second
                                     : ProposalFees{EXECUTION_DELAY};
    MONAD_ASSERT(
        proposals_
            .emplace(
                id_,
                std::make_pair(
                    block_number_,
                    parent.set(
                        block_number_ % EXECUTION_DELAY, std::move(fees_))))
            .second);
    fees_.clear();
}

void FeeBuffer::finalize(bytes32_t const &id)
{
    MONAD_ASSERT(proposals_.contains(id));
    std::erase_if(
        proposals_, [block_number = proposals_.at(id).first](auto const &it) {
            return it.second.first < block_number;
        });
}

FeeBufferResult FeeBuffer::get(uint64_t const i, Address const &a) const
{
    MONAD_ASSERT(proposals_.contains(id_));
    FeeBufferResult result{};
    bool found = false;
    auto const &proposals = proposals_.at(id_).second;
    for (unsigned j = 0; j < proposals.size(); ++j) {
        auto const &fees = proposals[j];
        if (!fees.contains(a)) {
            continue;
        }
        for (auto const &[k, fee] : fees.at(a)) {
            ++result.num_fees;
            result.cumulative_fee += fee;
            if ((j == block_number_ % EXECUTION_DELAY) && k == i) {
                MONAD_ASSERT(!found);
                found = true;
                result.tx_fee = fee;
                break;
            }
        }
    }
    MONAD_ASSERT(found);
    return result;
}

FeeBuffer make_fee_buffer(
    uint64_t const block_to_execute,
    std::function<std::tuple<
        bytes32_t, MonadConsensusBlockHeaderV1, std::vector<Transaction>>(
        uint64_t block)> const &read_header_and_transactions)
{
    FeeBuffer fee_buffer;
    for (uint64_t i = block_to_execute < EXECUTION_DELAY
                          ? 1
                          : block_to_execute - EXECUTION_DELAY + 1;
         i < block_to_execute;
         ++i) {
        auto const [id, header, transactions] = read_header_and_transactions(i);
        MONAD_ASSERT(header.execution_inputs.number == i);
        fee_buffer.set(header.execution_inputs.number, id, header.parent_id());
        for (uint64_t i = 0; i < transactions.size(); ++i) {
            auto const &txn = transactions[i];
            auto const fee = max_gas_cost(txn.gas_limit, txn.max_fee_per_gas);
            auto const sender = recover_sender(txn);
            MONAD_ASSERT(
                sender.has_value(), "transaction sender recovery failed");
            fee_buffer.note(i, sender.value(), fee);
        }
        fee_buffer.propose();
    }

    return fee_buffer;
}

MONAD_NAMESPACE_END
