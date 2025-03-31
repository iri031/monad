#pragma once

#include <monad/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/staticanalysis/expr.hpp>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>


#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct ExecutionResult;

struct CalleePredInfo {
    std::unordered_map<Address, bytes32_t> code_hashes;
    ExpressionPool epool;
    std::unordered_map<evmc::bytes32, Prediction> predictions;
    std::optional<Prediction*> lookup_callee(evmc::address runningAddress) {
        bytes32_t code_hash = code_hashes[runningAddress];
        //LOG_INFO("code_hash: {}, runningAddress: {}", code_hash, runningAddress);
        auto it = predictions.find(code_hash);
        if(it == predictions.end()) {
            return std::nullopt;
        }
        return &(it->second);
    }
};

uint64_t numPredictedFootprints();
uint64_t numTTPredictedFootprints();
std::chrono::duration<double> get_compile_footprints_time();
std::chrono::duration<double> get_footprint_time();

using IdealFP= std::vector<std::vector<std::set<evmc::address>>>;// [block][tx]
 // Start Generation Here
 inline void serializeIdealFP(const IdealFP &ideal_fp, const std::string &filename) {
     std::ofstream out(filename, std::ios::binary);
     if (!out) {
         // Could handle error silently or throw
         return;
     }

     // Write number of blocks
     size_t blocks_count = ideal_fp.size();
     out.write(reinterpret_cast<const char*>(&blocks_count), sizeof(blocks_count));

     // For each block
     for (auto const &block_fp : ideal_fp) {
         // Write number of transactions
         size_t tx_count = block_fp.size();
         out.write(reinterpret_cast<const char*>(&tx_count), sizeof(tx_count));

         // For each transaction
         for (auto const &tx_fp : block_fp) {
             // Write number of addresses
             size_t addr_count = tx_fp.size();
             out.write(reinterpret_cast<const char*>(&addr_count), sizeof(addr_count));

             // Write addresses
             for (auto const &addr : tx_fp) {
                 out.write(reinterpret_cast<const char*>(addr.bytes), sizeof(addr.bytes));
             }
         }
     }
 }

 inline void unserializeIdealFP(IdealFP &ideal_fp, const std::string &filename) {
     std::ifstream in(filename, std::ios::binary);
     if (!in) {
         throw std::runtime_error("Cannot open file for reading: " + filename);
     }

     ideal_fp.clear();

     // Read number of blocks
     size_t blocks_count = 0;
     in.read(reinterpret_cast<char*>(&blocks_count), sizeof(blocks_count));
     ideal_fp.resize(blocks_count);

     // For each block
     for (size_t b = 0; b < blocks_count; ++b) {
         // Read number of transactions
         size_t tx_count = 0;
         in.read(reinterpret_cast<char*>(&tx_count), sizeof(tx_count));
         ideal_fp[b].resize(tx_count);

         // For each transaction
         for (size_t t = 0; t < tx_count; ++t) {
             // Read number of addresses
             size_t addr_count = 0;
             in.read(reinterpret_cast<char*>(&addr_count), sizeof(addr_count));

             // Read addresses
             for (size_t a = 0; a < addr_count; ++a) {
                 evmc::address addr{};
                 in.read(reinterpret_cast<char*>(addr.bytes), sizeof(addr.bytes));
                 ideal_fp[b][t].insert(addr);
             }
         }
     }
 }

IdealFP & getIdealFP();
std::vector<std::set<evmc::address>> & blockFootprint(uint64_t blockNumber);
void setStartBlockNumber(uint64_t startBlockNumber);

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, Block &, BlockState &, BlockHashBuffer const &,
    fiber::PriorityPool &, CalleePredInfo &);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &, evmc_revision, Block &, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &, CalleePredInfo &);

MONAD_NAMESPACE_END
