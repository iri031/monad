# Execution event SDK

Execution events is Category Labs' high performance system for listening to
real-time data produced on the Monad blockchain. It is designed for consumers
that need the lowest latency possible, and is overkill for typical users
-- see the [alternatives section](#alternatives-to-execution-events) for
more convenient ways to consume Monad blockchain data.

## What are "execution events"?

Category Labs develops and maintains node software for the EVM-compatible
[Monad](https:://www.monad.xyz) blockchain. Like legacy
[Ethereum nodes](https://ethereum.org/en/developers/docs/nodes-and-clients/node-architecture/]),
Category's Monad node implementation splits the consensus and execution tasks
into two different programs. Each program is a separate UNIX background
process (or "daemon"); as in other Ethereum node architectures, the two tasks
are called "consensus" (agreement about blocks) and "execution" (EVM execution
of blocks).

The execution daemon contains a shared-memory communication system that
records most actions taken by the EVM during transaction execution. The
raw binary records of these EVM actions are called "execution events".

Third-party applications that need the highest performance can run on the
same host as the node software, and directly consume this event data from
shared memory.

To read the events from shared memory, your third-party application calls
functions in the execution event SDK, our real-time data library that
reads the EVM records from this shared memory channel.

## Execution events documentation

- [Getting started](getting-started.md) - describes how to build the SDK
  source code and run the example program
- [Events overview](overview.md) - explains the core concepts in the
  execution events system
- [Event rings in detail](event-ring.md) - XXX
- API documentation - overview of our programming libraries, which are
  provided for several programming languages
   - [C API](c-api.md)
   - [Rust API](rust-api.md)
- [Consensus events](consensus-events.md) - although consensus is a
  separate process from execution, execution publishes some information
  from consensus that is essential for understanding finalization
- [Advanced topics](advanced.md) - documentation for advanced users and
  for software developers who contribute to the execution daemon source
  code

## Alternatives to execution events

Category Lab's node software includes an "RPC server" component. The RPC
server supports two simple ways to read blockchain data:

1. The typical [JSON RPC](https://docs.monad.xyz/reference/) endpoints for
   other EVM blockchain clients (e.g., Geth) are supported
2. The Geth [real time events](https://geth.ethereum.org/docs/interacting-with-geth/rpc/pubsub)
   WebSocket protocol (i.e., `eth_subscribe`) is also supported, along with some
   extensions *TODO: link the extension docs*

Both of these access methods are somewhat standardized across EVM
implementations and simpler to use than execution events. The execution events
system is designed for specialized applications, such as running an indexer
platform or applications that need the lowest latency possible (e.g., market
making).

## Comparisons with other data systems

A brief comparison with low latency systems in other blockchain
software:

- __Geth Live Tracing__ [(link)](https://geth.ethereum.org/docs/developers/evm-tracing/live-tracing) - "hook" based API: your code is loaded
  into the Geth node as a plugin, and is run synchronously (via callbacks)
  during execution
- __Reth ExEx__ [(link)](https://www.paradigm.xyz/2024/05/reth-exex) and [(link)](https://reth.rs/developers/exex/exex.html) - async function based API:
  your code is loaded into a Reth node; execution sees events after the fact
  rather than synchronously
- __Solana Geyser__ [(link)](https://www.helius.dev/blog/solana-geyser-plugins-streaming-data-at-the-speed-of-light) - "hook" based API, a plugin that runs inside
  a Solana validator and invokes callbacks during execution

All three of these are different from our approach. In our approach:

- You are seeing events "as-they-happen", as in the Geth Live Tracer and
  Solana Geyser. Unlike these approaches, your code is not running as a
  plugin inside the execution engine, but in parallel (about 50-100
  nanoseconds after) in a separate process
- Like the Geth Live Tracer (but unlike Reth's ExEx) you see each "piece"
  of the transaction -- each log, each balance change, etc. -- as a
  separate event
- Unlike the Geth Live Tracer or Geyser, you do not install "hooks" and
  receive callbacks; instead you continuously poll for new event records,
  iterating through any new events that are returned to you (and ignoring
  events that you are not interested in)
- Because the system is based on shared memory ring buffers, you can lose
  data if your consumer is too slow -- you must keep up!
