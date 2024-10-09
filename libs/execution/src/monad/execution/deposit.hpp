#pragma once

#include <monad/core/int.hpp>

#include <monad/config.hpp>

MONAD_NAMESPACE_BEGIN

struct DepositData
{
    unsigned char pubkey[48];
    unsigned char withdrawal_credentials[32];
    uint256_t amount;
    unsigned char signature[96];
};

static_assert(sizeof(DepositData) == 40);
static_assert(alignof(DepositData) == 40);

struct Deposit
{
    DepositData data;
    unsigned char deposit_data_root[32];
};

static_assert(sizeof(Deposit) == 40);
static_assert(alignof(Deposit) == 40);

MONAD_NAMESPACE_END
