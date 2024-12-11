#include "parallel_commit_system.hpp"

MONAD_NAMESPACE_BEGIN

void ParallelCommitSystem::waitForTrasactionsAccessingAddresses(
    txindex_t myindex, std::vector<evmc::address> const) {
    promises[myindex].get_future().wait();
}

void ParallelCommitSystem::notifyDone(txindex_t myindex) {
    promises[myindex + 1].set_value();
}

ParallelCommitSystem::ParallelCommitSystem(txindex_t num_transactions) {
    promises = new boost::fibers::promise<void>[num_transactions + 1];
    promises[0].set_value();
}

ParallelCommitSystem::~ParallelCommitSystem() {
    delete[] promises;
}

MONAD_NAMESPACE_END