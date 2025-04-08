#pragma once

#include <monad/chain/chain_config.h>

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_state_override;
struct monad_eth_call_executor;

struct monad_state_override *monad_state_override_create();

void monad_state_override_destroy(struct monad_state_override *);

void add_override_address(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len);

void set_override_balance(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *balance, size_t balance_len);

void set_override_nonce(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint64_t nonce);

void set_override_code(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *code, size_t code_len);

void set_override_state_diff(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *key, size_t key_len, uint8_t const *value,
    size_t valuen_len);

void set_override_state(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *key, size_t key_len, uint8_t const *value,
    size_t valuen_len);

typedef struct monad_eth_call_result
{
    int status_code;
    int64_t gas_used;
    int64_t gas_refund;

    uint8_t *output_data;
    size_t output_data_len;

    char *message;
} monad_eth_call_result;

void monad_eth_call_result_release(monad_eth_call_result *);

struct monad_eth_call_executor *monad_eth_call_executor_create(
    unsigned num_threads, unsigned num_fibers, unsigned node_lru_size,
    char const *dbpath);

void monad_eth_call_executor_destroy(struct monad_eth_call_executor *);

void monad_eth_call_executor_submit(
    struct monad_eth_call_executor *, enum monad_chain_config,
    uint8_t const *rlp_txn, size_t rlp_txn_len, uint8_t const *rlp_header,
    size_t rlp_header_len, uint8_t const *rlp_sender, size_t rlp_sender_len,
    uint64_t block_number, uint64_t block_round,
    struct monad_state_override const *,
    void (*complete)(monad_eth_call_result *, void *user), void *user);

#ifdef __cplusplus
}
#endif
