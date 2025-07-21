#pragma once

/**
 * @file
 *
 * C layout-compatible types describing Ethereum blocks and transactions
 */

#include <category/execution/ethereum/core/base_ctypes.h>
#include <stdint.h>

// clang-format off
#ifdef __cplusplus
extern "C"
{
#endif

/// EIP-2718 code determining the transaction type
enum monad_c_transaction_type : uint8_t
{
    MONAD_TXN_LEGACY = 0,
    MONAD_TXN_EIP2930 = 1,
    MONAD_TXN_EIP1559 = 2,
};

/// Entry in a EIP-2930 storage access warmup list
struct monad_c_access_list_entry
{
    monad_c_address address;    ///< E_a: addr of account whose storage to warm
    uint32_t storage_key_count; ///< Size of trailing E_s storage key array
};

/// Fields of an Ethereum transaction that are recognized by the monad EVM
/// implementation.
///
/// This type contains the fixed-size fields present in any supported
/// transaction type. If a transaction type does not support a particular field,
/// it will be zero-initialized.
struct monad_c_eth_txn_header
{
    enum monad_c_transaction_type
        txn_type;                       ///< EIP-2718 transaction type
    monad_c_uint256_ne chain_id;        ///< T_c: EIP-155 blockchain identifier
    uint64_t nonce;                     ///< T_n: num txns sent by this sender
    uint64_t gas_limit;                 ///< T_g: max usable gas (upfront xfer)
    monad_c_uint256_ne max_fee_per_gas; ///< T_m in EIP-1559 txns or T_p (gasPrice)
    monad_c_uint256_ne
        max_priority_fee_per_gas;       ///< T_f in EIP-1559 txns, 0 otherwise
    monad_c_uint256_ne value;           ///< T_v: wei xfered or contract endowment
    monad_c_address to;                 ///< T_t: recipient
    bool is_contract_creation;          ///< True -> interpret T_t == 0 as null
    monad_c_uint256_ne r;               ///< T_r: r value of ECDSA signature
    monad_c_uint256_ne s;               ///< T_s: s value of ECDSA signature
    bool y_parity;                      ///< Signature Y parity (see YP App. F)
    uint32_t data_length;               ///< Length of trailing `data` array
    uint32_t access_list_count;         ///< # of EIP-2930 AccessList entries
};

/// Result of executing a valid transaction
///
/// This type is designed for incremental, out-of-order reporting of transaction
/// results, so it differs from the formal definition of an Ethereum receipt
/// (e.g., gas used is not cumulative)
struct monad_c_eth_txn_receipt
{
    bool status;        ///< EIP-658 status code
    uint32_t log_count; ///< Number of log entries
    uint64_t gas_used;  ///< Gas used by this txn only (not R_u)
};

/// Data record produced during the execution of a transaction
struct monad_c_eth_txn_log
{
    uint32_t index;          ///< Index of log in series
    monad_c_address address; ///< Address of contract generating log
    uint8_t topic_count;     ///< Size of hash32 topic array after header
    uint32_t data_length;    ///< Length of log data placed after header
};

/// Account state sigma[a] (except for storage root hash, sigma[a]_s)
struct monad_c_eth_account_state
{
    uint64_t nonce;             ///< sigma[a]_n: num tx sent from address
    monad_c_uint256_ne balance; ///< sigma[a]_b: wei owned by address
    monad_c_bytes32 code_hash;  ///< sigma[a]_c: EVM code hash
};

/// Fields of an Ethereum block header which are known at the start of execution
struct monad_c_eth_block_exec_input
{
    monad_c_bytes32 ommers_hash;         ///< H_o: hash of ommer blocks
    monad_c_address beneficiary;         ///< H_c: recipient addr of prio gas fees
    monad_c_bytes32 transactions_root;   ///< H_t: hash of block txn list
    uint64_t difficulty;                 ///< H_d: PoW difficulty scaling param
    uint64_t number;                     ///< H_i: # of ancestor blocks ("height")
    uint64_t gas_limit;                  ///< H_l: max gas expenditure we're allowed
    uint64_t timestamp;                  ///< H_s: UNIX epoch timestamp of block inception
    monad_c_bytes32 extra_data;          ///< H_x: extra metadata about this block
    uint64_t extra_data_length;          ///< Number of bytes used in H_x
    monad_c_bytes32 prev_randao;         ///< H_a: source of randomness
    monad_c_b64 nonce;                   ///< H_n: PoW puzzle solution; now zero
    monad_c_uint256_ne base_fee_per_gas; ///< H_f: wei burned per unit gas
    monad_c_bytes32 withdrawals_root;    ///< H_w: consensus-initiated withdrawals
    uint64_t txn_count;                  ///< Number of transactions in block
};

/// Fields of an Ethereum block header which are produced as a result of
/// execution
struct monad_c_eth_block_exec_output
{
    monad_c_bytes32 state_root;    ///< H_r: MPT root hash of state trie
    monad_c_bytes32 receipts_root; ///< H_e: MPT root hash of receipt trie
    monad_c_bloom256 logs_bloom;   ///< H_b: bloom filter of transaction logs
    uint64_t gas_used;             ///< H_g: gas used by all txns in block
};

// clang-format on

#ifdef __cplusplus
} // extern "C"
#endif
