#include <category/mpt2/child_data.hpp>
#include <category/mpt2/compute.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

void ChildData::finalize(Node::UniquePtr ptr, Compute &compute)
{
    MONAD_DEBUG_ASSERT(is_valid());
    MONAD_ASSERT(ptr != nullptr);
    node = std::move(ptr);
    auto const length = compute.compute(data, node.get());
    MONAD_DEBUG_ASSERT(length <= std::numeric_limits<uint8_t>::max());
    data_size = static_cast<uint8_t>(length);
    subtrie_min_version = calc_min_version(*node);
}

void ChildData::copy_old_child(Node &old, unsigned const branch)
{
    MONAD_DEBUG_ASSERT(branch < 16);
    this->branch = static_cast<uint8_t>(branch);
    auto const index = old.to_child_index(branch);
    auto const old_data = old.child_data_view(index);
    memcpy(&data, old_data.data(), old_data.size());
    MONAD_DEBUG_ASSERT(old_data.size() <= std::numeric_limits<uint8_t>::max());
    data_size = static_cast<uint8_t>(old_data.size());

    offset = old.fnext(index);
    min_offset_fast = old.min_offset_fast(index);
    min_offset_slow = old.min_offset_slow(index);
    subtrie_min_version = old.subtrie_min_version(index);
}

MONAD_MPT2_NAMESPACE_END
