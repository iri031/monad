# Getting started with execution events

In this guide, we will:

1. Set up our own Monad node, so that we have a local execution process
   writing execution events
2. Compile the SDK, including the example program
3. Run the example program, which prints ASCII representations of the
   execution events to `stdout`; this allows you to watch the events
   produced by execution in real time

## Setup and installation

### Running your own node

The execution events SDK uses a shared memory communication system, in
which the node's EVM execution daemon acts a publisher. Consequently,
in order to use it, you must run your own Monad blockchain node.

The execution daemon will write the events into shared memory, and the
example program (and later, your real application) will run on the same
host, and read from this shared memory.

XXX instructions on running node
YYY additional commmand line stuff

### Building the SDK

To read the real-time data published by the EVM, client software uses the
"execution event SDK." This is offered for both the C and Rust programming
languages.

#### Instructions for C

XXX

#### Instructions for Rust

XXX

## First steps

The easiest way to get acquainted with the executione event system is to:

1. Read the short [overview](overview.md) explaining what execution events
   are

2. Build and run the SDK example program, which prints execution events to
   the terminal. There are two such programs: one for C and one for Rust.
   - For C, XXX
   - For Rust, XXX

3. Read the documentation in more detail:
   XXX

4. Look at a more sophisticated program that
   - For C, XXX eventcap
   - For Rust, XXX block??

5. Before using the SDK, make sure you understand the
   [consensus events](consensus-events.md) and what they mean!

XXX example program
YYY install

## What do to next?

XXX
