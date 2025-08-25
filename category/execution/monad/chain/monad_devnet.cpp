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
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_devnet_alloc.hpp>
#include <category/execution/monad/chain/monad_revision.h>

MONAD_NAMESPACE_BEGIN

Chain &get_monad_devnet(uint64_t /*timestamp*/)
{
    static const uint256_t chain_id{20143};

    static const GenesisState genesis_state = []{
        BlockHeader header;
        header.difficulty = 17179869184;
        header.gas_limit = 5000;
        intx::be::unsafe::store<uint64_t>(header.nonce.data(), 66);
        header.extra_data =
            evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                           "db3db69cbdb7a38e1e50b1b82fa")
                .value();
        return GenesisState{header, MONAD_DEVNET_ALLOC};
    }();

    static MonadChain2<MONAD_FOUR> chain{chain_id, genesis_state};

    return chain;
}

MONAD_NAMESPACE_END
