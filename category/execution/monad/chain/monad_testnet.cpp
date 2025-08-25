// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/monad/chain/monad_revision.h>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet_alloc.hpp>

MONAD_NAMESPACE_BEGIN

Chain &get_monad_testnet(uint64_t const timestamp)
{
    static uint256_t const chain_id{10143};

    static GenesisState const genesis_state = [] {
        BlockHeader header;
        header.difficulty = 17179869184;
        header.gas_limit = 5000;
        intx::be::unsafe::store<uint64_t>(header.nonce.data(), 66);
        header.extra_data =
            evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                           "db3db69cbdb7a38e1e50b1b82fa")
                .value();
        return GenesisState{header, MONAD_TESTNET_ALLOC};
    }();

    if (MONAD_LIKELY(timestamp >= 1755005400)) { // 2025-08-12T13:30:00.000Z
        static MonadChain2<MONAD_THREE> chain{chain_id, genesis_state};
        return chain;
    }
    else if (timestamp >= 1741978800) { // 2025-03-14T19:00:00.000Z
        static MonadChain2<MONAD_TWO> chain{chain_id, genesis_state};
        return chain;
    }
    else if (timestamp >= 1739559600) { // 2025-02-14T19:00:00.000Z
        static MonadChain2<MONAD_ONE> chain{chain_id, genesis_state};
        return chain;
    }
    static MonadChain2<MONAD_ZERO> chain{chain_id, genesis_state};
    return chain;
}

MONAD_NAMESPACE_END
