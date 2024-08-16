#pragma once

#include <monad/core/block.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/block_hash_buffer.hpp>

#include <cstdint>
#include <filesystem>
#include <memory>
#include <string>
#include <vector>

#include <boost/outcome/try.hpp>

using namespace monad;

struct monad_evmc_result
{
    int status_code;
    std::vector<uint8_t> output_data;
    std::string message;
    int64_t gas_used;
    int64_t gas_refund;

    int get_status_code() const;
    std::vector<uint8_t> get_output_data() const;
    std::string get_message() const;
    int64_t get_gas_used() const;
    int64_t get_gas_refund() const;
};

monad_evmc_result eth_call(
    std::vector<uint8_t> const &rlp_txn, std::vector<uint8_t> const &rlp_header,
    std::vector<uint8_t> const &rlp_sender, uint64_t block_number,
    std::string const &triedb_path, std::string const &blockdb_path);

Result<evmc::Result> eth_call_impl(
    Transaction const &txn, BlockHeader const &header,
    uint64_t const block_number, Address const &sender,
    BlockHashBuffer const &buffer,
    std::vector<std::filesystem::path> const &dbname_paths);
