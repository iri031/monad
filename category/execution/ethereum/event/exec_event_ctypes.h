#pragma once

/**
 * @file
 *
 * Definitions of event payloads used with the EXEC event ring
 */

#include <category/core/event/event_metadata.h>
#include <category/execution/ethereum/core/eth_ctypes.h>
#include <stdint.h>

// clang-format off
#ifdef __cplusplus
extern "C"
{
#endif

/// Each type of event is assigned a unique value in this enumeration
enum monad_exec_event_type : uint16_t
{
    MONAD_EXEC_NONE,
    MONAD_EXEC_BLOCK_START,
    MONAD_EXEC_BLOCK_REJECT,
    MONAD_EXEC_BLOCK_PERF_EVM_ENTER,
    MONAD_EXEC_BLOCK_PERF_EVM_EXIT,
    MONAD_EXEC_BLOCK_END,
    MONAD_EXEC_BLOCK_QC,
    MONAD_EXEC_BLOCK_FINALIZED,
    MONAD_EXEC_BLOCK_VERIFIED,
    MONAD_EXEC_TXN_START,
    MONAD_EXEC_TXN_REJECT,
    MONAD_EXEC_TXN_PERF_EVM_ENTER,
    MONAD_EXEC_TXN_PERF_EVM_EXIT,
    MONAD_EXEC_TXN_EVM_OUTPUT,
    MONAD_EXEC_TXN_LOG,
    MONAD_EXEC_TXN_CALL_FRAME,
    MONAD_EXEC_TXN_END,
    MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER,
    MONAD_EXEC_ACCOUNT_ACCESS,
    MONAD_EXEC_STORAGE_ACCESS,
    MONAD_EXEC_EVM_ERROR,
};

/// Stored in event descriptor's `user` array to tag the block & transaction
/// context of event
enum monad_exec_flow_type : uint8_t
{
    MONAD_FLOW_BLOCK_SEQNO = 0,
    MONAD_FLOW_TXN_ID = 1,
    MONAD_FLOW_ACCOUNT_INDEX = 2,
};

/// Identifies a unique block that has been proposed by the consensus algorithm;
/// used to refer to a block before it is finalized.
///
/// Once a block is canonically appended to the block chain, it becomes uniquely
/// identified by a (sequentially increasing) block number, also called a "block
/// height." The inclusion of a block on the blockchain is the goal of the
/// consensus algorithm, and is called "finalization."
///
/// When a block it first constructed, it is constructed assuming it will become
/// the next block number, `B`. Prior to finalization, consensus nodes are still
/// trying to agree whether or not this candidate block will become block `B`.
///
/// During this time, multiple blocks could be proposed, some of which are
/// competing candidates to become the same block number `B`. For performance
/// reasons, the execution daemon is allowed to speculatively execute blocks in
/// the EVM before they finalize in consensus. Consequently, even blocks that
/// never become part of the blockchain may produce execution events; execution
/// events may describe transactions that "never happen" on chain.
///
/// Thus, when a block number is seen during an event, e.g., `BLOCK_START`, it
/// is not necessarily the case that the associated block will be added to the
/// blockchain as this block number (or at all).
///
/// The information in this "tag" object is used to track a block as it is
/// operated on by the consensus algorithm. The (not yet unique) `block_number`
/// is the number the block _will_ have, if it eventually gets finalized. The
/// `id` field uniquely identifies the block contents, vs. all the other
/// proposals of different blocks to become the same `block_number`. `id` can be
/// used to track this specific block before finalization.
struct monad_exec_block_tag
{
    monad_c_bytes32 id;    ///< Monad consensus unique ID for block
    uint64_t block_number; ///< Proposal is to become this block
};

/// Event recorded at the start of block execution
struct monad_exec_block_start
{
    struct monad_exec_block_tag
        block_tag;                      ///< Execution is for this block
    uint64_t round;                     ///< Round when block was proposed
    uint64_t epoch;                     ///< Epoch when block was proposed
    monad_c_bytes32 parent_eth_hash;    ///< Hash of Ethereum parent block
    monad_c_uint256_ne chain_id;        ///< Block chain we're associated with
    struct monad_c_eth_block_exec_input
        exec_input;                     ///< Ethereum execution inputs
};

/// Event recorded when a block is rejected (i.e., is invalid)
///
/// This corresponds to a value in the `BlockError` enumeration in
/// `validate_block.hpp`, in the execution repo source code.
typedef uint32_t monad_exec_block_reject;

/// Event recorded upon successful block execution
struct monad_exec_block_end
{
    monad_c_bytes32 eth_block_hash;      ///< Hash of Ethereum block
    struct monad_c_eth_block_exec_output
        exec_output;                     ///< Ethereum execution outputs
};

/// Event recorded when a proposed block obtains a quorum certificate
struct monad_exec_block_qc
{
    struct monad_exec_block_tag
        block_tag;              ///< QC for proposal with this block
    uint64_t round;             ///< Round of proposal vote
    uint64_t epoch;             ///< Epoch of proposal vote
};

/// Event recorded when consensus finalizes a block
typedef struct monad_exec_block_tag monad_exec_block_finalized;

/// Event recorded when consensus verifies the state root of a finalized block
struct monad_exec_block_verified
{
    uint64_t block_number; ///< Number of verified block
};

/// Event recorded when transaction processing starts
struct monad_exec_txn_start
{
    uint64_t ingest_epoch_nanos;  ///< Epoch nanos before sender recovery
    monad_c_bytes32 txn_hash;     ///< Keccak hash of transaction RLP
    monad_c_address sender;       ///< Recovered sender address
    struct monad_c_eth_txn_header
        txn_header;               ///< Transaction header
};

/// Event recorded when a transaction is rejected (i.e., is invalid)
///
/// This corresponds to a value in the `TransactionError` enumeration in
/// `validate_transaction.hpp`, in the execution repo source code.
typedef uint32_t monad_exec_txn_reject;

/// Event recorded when transaction execution halts.
///
/// This is a "header" event: it appears before all other transaction output
/// events, namely all the TXN_LOG and TXN_CALL_FRAME events associated with
/// this transaction. It is emitted first, to announces the total number of log
/// and call frame events that the reader should expect. After all transaction
/// are emitted, an ACCOUNT_ACCESS_LIST_HEADER event with transaction scope will
/// be emitted, announcing all state change accesses in the scope of this
/// transaction.
///
/// Once all execution outputs have been emitted for a particular transaction
/// number, a TXN_END event will be emitted to mark the end of all that
/// transaction's events.
struct monad_exec_txn_evm_output
{
    struct monad_c_eth_txn_receipt
        receipt;                   ///< Incremental Ethereum receipt
    uint32_t call_frame_count;     ///< Number of call frames
};

/// Event recorded when a transaction emits a LOG
typedef struct monad_c_eth_txn_log monad_exec_txn_log;

/// Event recorded when a call frame is emitted.
///
/// Trace information about an execution context that was created during an EVM
/// contract invocation ("call"), or contract creation.
///
/// Formally, the EVM operates through concepts called 'message calls' and
/// 'contract creations'. Each of these defines an execution environment, which
/// contains data such as the account causing the code to execute. A formal list
/// of all the items in the environment is part of the official specification.
///
/// Each call (and contract creation) gets its own environment. The environments
/// are set up in different ways, depending on how the call occurs (e.g., a CALL
/// vs. DELEGATECALL opcode). A call frame is a summary of the inputs and
/// outputs to an execution environment, whether the halting was normal or
/// exceptional, and other information useful for tracing the call tree.
struct monad_exec_txn_call_frame
{
    uint32_t index;              ///< Array index of call frame
    monad_c_address caller;      ///< Address initiating call
    monad_c_address call_target; ///< Address receiving call (or deployment addr)
    uint8_t opcode;              ///< EVM opcode that creates frame
    monad_c_uint256_ne value;    ///< I_v: value passed to account during execution
    uint64_t gas;                ///< g: gas available for message execution
    uint64_t gas_used;           ///< Gas used by call
    int32_t evmc_status;         ///< evmc_status_code of call
    uint64_t depth;              ///< I_e: depth of call context stack
    uint64_t input_length;       ///< Length of trailing call input
    uint64_t return_length;      ///< Length of trailing return data
};

/// Context in which EVM accessed / modified an account
enum monad_exec_account_access_context : uint8_t
{
    MONAD_ACCT_ACCESS_BLOCK_PROLOGUE = 0,
    MONAD_ACCT_ACCESS_TRANSACTION = 1,
    MONAD_ACCT_ACCESS_BLOCK_EPILOGUE = 2,
};

/// Header event that precedes a variably-sized list of account_access objects
struct monad_exec_account_access_list_header
{
    uint32_t entry_count;                  ///< Number of account_access_entry events
    enum monad_exec_account_access_context
        access_context;                    ///< Context of account accesses
};

/// Event emitted when an account is read or written
struct monad_exec_account_access
{
    uint32_t index;                        ///< Index in accessed account list
    monad_c_address address;               ///< Address of account
    enum monad_exec_account_access_context
        access_context;                    ///< Context of account access
    bool is_balance_modified;              ///< True -> modified_balance meaningful
    bool is_nonce_modified;                ///< True -> modified_nonce meaningful
    struct monad_c_eth_account_state
        prestate;                          ///< Read (or original) balance
    monad_c_uint256_ne modified_balance;   ///< New balance, if modified
    uint64_t modified_nonce;               ///< New nonce, if modified
    uint32_t storage_key_count;            ///< Number of trailing storage_access events
    uint32_t transient_count;              ///< As above, but for transient storage
};

/// Event emitted for each account storage key that is accessed
struct monad_exec_storage_access
{
    monad_c_address address;               ///< Address of storage account
    uint32_t index;                        ///< Index of storage records in this context
    enum monad_exec_account_access_context
        access_context;                    ///< Context of account access
    bool modified;                         ///< True -> new_value meaningful
    bool transient;                        ///< True -> is transient storage
    monad_c_bytes32 key;                   ///< Storage key accessed / modified
    monad_c_bytes32 start_value;           ///< Read (or original) value
    monad_c_bytes32 end_value;             ///< New value, if modified
};

/// Error occurred in execution process (not a validation error)
struct monad_exec_evm_error
{
    uint64_t domain_id;  ///< Boost.Outcome domain id of error
    int64_t status_code; ///< Boost.Outcome status code of error
};

// clang-format on

extern struct monad_event_metadata const g_monad_exec_event_metadata[21];
extern uint8_t const g_monad_exec_event_metadata_hash[32];

constexpr char MONAD_EVENT_DEFAULT_EXEC_RING_PATH[] =
    "/dev/hugepages/monad-exec-events";

#ifdef __cplusplus
} // extern "C"
#endif
