#include <stdint.h>

#include <category/core/event/event_metadata.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_metadata const g_monad_exec_event_metadata[21] = {
    [MONAD_EXEC_NONE] =
        {.event_type = MONAD_EXEC_NONE,
         .c_name = "MONAD_EXEC_NONE",
         .description = "reserved code so that 0 remains invalid"},

    [MONAD_EXEC_BLOCK_START] =
        {.event_type = MONAD_EXEC_BLOCK_START,
         .c_name = "BLOCK_START",
         .description = "Event recorded at the start of block execution"},

    [MONAD_EXEC_BLOCK_REJECT] =
        {.event_type = MONAD_EXEC_BLOCK_REJECT,
         .c_name = "BLOCK_REJECT",
         .description =
             "Event recorded when a block is rejected (i.e., is invalid)"},

    [MONAD_EXEC_BLOCK_PERF_EVM_ENTER] =
        {.event_type = MONAD_EXEC_BLOCK_PERF_EVM_ENTER,
         .c_name = "BLOCK_PERF_EVM_ENTER",
         .description =
             "Performance marker event recorded at the start of core EVM "
             "execution (after validation and sender recovery)"},

    [MONAD_EXEC_BLOCK_PERF_EVM_EXIT] =
        {.event_type = MONAD_EXEC_BLOCK_PERF_EVM_EXIT,
         .c_name = "BLOCK_PERF_EVM_EXIT",
         .description = "Performance marker event recorded when all "
                        "transaction execution is finished"},

    [MONAD_EXEC_BLOCK_END] =
        {.event_type = MONAD_EXEC_BLOCK_END,
         .c_name = "BLOCK_END",
         .description = "Event recorded upon successful block execution"},

    [MONAD_EXEC_BLOCK_QC] =
        {.event_type = MONAD_EXEC_BLOCK_QC,
         .c_name = "BLOCK_QC",
         .description = "Event recorded when a proposed block obtains a quorum "
                        "certificate"},

    [MONAD_EXEC_BLOCK_FINALIZED] =
        {.event_type = MONAD_EXEC_BLOCK_FINALIZED,
         .c_name = "BLOCK_FINALIZED",
         .description = "Event recorded when consensus finalizes a block"},

    [MONAD_EXEC_BLOCK_VERIFIED] =
        {.event_type = MONAD_EXEC_BLOCK_VERIFIED,
         .c_name = "BLOCK_VERIFIED",
         .description = "Event recorded when consensus verifies the state root "
                        "of a finalized block"},

    [MONAD_EXEC_TXN_START] =
        {.event_type = MONAD_EXEC_TXN_START,
         .c_name = "TXN_START",
         .description = "Event recorded when transaction processing starts"},

    [MONAD_EXEC_TXN_REJECT] =
        {.event_type = MONAD_EXEC_TXN_REJECT,
         .c_name = "TXN_REJECT",
         .description = "Event recorded when a transaction is rejected (i.e., "
                        "is invalid)"},

    [MONAD_EXEC_TXN_PERF_EVM_ENTER] =
        {.event_type = MONAD_EXEC_TXN_PERF_EVM_ENTER,
         .c_name = "TXN_PERF_EVM_ENTER",
         .description = "Performance marker event recorded at the start of EVM "
                        "execution (after sender recovery)"},

    [MONAD_EXEC_TXN_PERF_EVM_EXIT] =
        {.event_type = MONAD_EXEC_TXN_PERF_EVM_EXIT,
         .c_name = "TXN_PERF_EVM_EXIT",
         .description =
             "Performance marker event recorded at the end of EVM execution"},

    [MONAD_EXEC_TXN_EVM_OUTPUT] =
        {.event_type = MONAD_EXEC_TXN_EVM_OUTPUT,
         .c_name = "TXN_EVM_OUTPUT",
         .description = "Event recorded when transaction execution halts."},

    [MONAD_EXEC_TXN_LOG] =
        {.event_type = MONAD_EXEC_TXN_LOG,
         .c_name = "TXN_LOG",
         .description = "Event recorded when a transaction emits a LOG"},

    [MONAD_EXEC_TXN_CALL_FRAME] =
        {.event_type = MONAD_EXEC_TXN_CALL_FRAME,
         .c_name = "TXN_CALL_FRAME",
         .description = "Event recorded when a call frame is emitted."},

    [MONAD_EXEC_TXN_END] =
        {.event_type = MONAD_EXEC_TXN_END,
         .c_name = "TXN_END",
         .description =
             "Event recorded to mark the end of events for this transaction"},

    [MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER] =
        {.event_type = MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER,
         .c_name = "ACCOUNT_ACCESS_LIST_HEADER",
         .description = "Header event that precedes a variably-sized list of "
                        "account_access objects"},

    [MONAD_EXEC_ACCOUNT_ACCESS] =
        {.event_type = MONAD_EXEC_ACCOUNT_ACCESS,
         .c_name = "ACCOUNT_ACCESS",
         .description = "Event emitted when an account is read or written"},

    [MONAD_EXEC_STORAGE_ACCESS] =
        {.event_type = MONAD_EXEC_STORAGE_ACCESS,
         .c_name = "STORAGE_ACCESS",
         .description =
             "Event emitted for each account storage key that is accessed"},

    [MONAD_EXEC_EVM_ERROR] =
        {.event_type = MONAD_EXEC_EVM_ERROR,
         .c_name = "EVM_ERROR",
         .description =
             "Error occurred in execution process (not a validation error)"},
};

uint8_t const g_monad_exec_event_metadata_hash[32] = {
    0xdd, 0xc5, 0x8d, 0x9a, 0xfc, 0xab, 0xb6, 0xae, 0x55, 0xd5, 0x25,
    0xd2, 0x81, 0xef, 0x9f, 0xd2, 0xf9, 0xb4, 0xdb, 0xce, 0xb2, 0x7a,
    0xc1, 0x18, 0x06, 0x7c, 0xda, 0xfd, 0x70, 0xe9, 0x01, 0x6b,
};

#ifdef __cplusplus
} // extern "C"
#endif
