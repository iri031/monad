#pragma once

#include <monad/chain/chain_config.h>
#include <monad/core/intx.h>

#include <evmc/evmc.h>

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_mpt_db;

enum monad_eth_call_result_status
{
    MONAD_ETH_CALL_SUCCESS,
    MONAD_ETH_CALL_FAILURE_BLOCK_HASH_BUFFER,
};

struct monad_eth_call_result
{
    enum monad_eth_call_result_status status;
    struct evmc_result result;
};

struct monad_eth_call_transaction
{
    unsigned char from[20];
    unsigned char to[20];
    uint64_t gas;
    unsigned char gas_price[MONAD_UINT256_SIZE];
    unsigned char value[MONAD_UINT256_SIZE];
    unsigned char const *data;
    size_t data_size;
};

struct monad_eth_call_state_override_item
{
    unsigned char key[32];
    unsigned char value[32];
};

struct monad_eth_call_state_override
{
    unsigned char addr[20];
    unsigned char balance[MONAD_UINT256_SIZE];
    uint64_t nonce;
    unsigned char const *code;
    size_t code_size;
    bool incarnation;
    struct monad_eth_call_state_override_item const *state;
    size_t state_size;
};

struct monad_eth_call_result monad_eth_call(
    enum monad_chain_config, struct monad_mpt_db *,
    struct monad_eth_call_transaction const *, uint64_t block_number,
    struct monad_eth_call_state_override const *, size_t);

struct monad_db;

#ifdef __cplusplus
}
#endif
