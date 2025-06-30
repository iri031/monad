# The `monad` execution event system

The `monad` execution daemon includes a system for recording events that occur
during transaction processing. An "event" is a notification that the EVM has
performed some action, such as "an account balance has been updated" or "a new
block has started executing." `monad` EVM events can be observed by external
third-party applications, using a high-performance inter-process communication
channel.

## Overview of events

There are two parts to the event system:

1. The `monad` execution daemon is the *writer* of all events
2. An external application can become a *reader* of events using the C
   library `libmonad_event` (a Rust implementation is also available)

This documentation file provides a general overview of the event system, and
describes how to use `libmonad_event` as a reader. Even if your intention is
to use the Rust SDK, most of the information applies to both libraries.

### Basic operation

#### What is an event?

Events are made up of two components:

1. The *event descriptor* is a fixed-size (currently 64 byte) object describing
   an event that has happened. It contains the event's type, a sequence number,
   and a timestamp.
2. The *event payload* is a variably-sized piece of extra data about the event,
   which is specific to the event type. For example, a "transaction log" event
   describes a single EVM log record emitted by a transaction, and its payload
   contains the contract address, the log topics, and the log data. Some of
   the fields in the event descriptor not already mentioned are used to
   communicate where in shared memory the payload bytes are located, and the
   payload's length.

#### Where do events live?

When an event occurs, `monad` inserts an event descriptor into a ring
buffer that lives in a shared memory segment. Event payloads are stored
in an array (in a separate shared memory segment) called the "payload
buffer." The diagram below illustrates the layout of these shared
memory structures:

```
  ╔═Event descriptor array════════...════════════════════════════════╗
  ║                                                                  ║
  ║ ┌────────────┐ ┌────────────┐     ┌────────────┐  ┌────────────┐ ║
  ║ │   Event    │ │   Event    │     │   Event    │  │░░░░░░░░░░░░│ ║
  ║ │ descriptor │ │ descriptor │     │ descriptor │  │░░░ empty ░░│ ║
  ║ │     1      │ │     2      │     │     N      │  │░░░░░░░░░░░░│ ║
  ║ └┬───────────┘ └┬───────────┘     └┬───────────┘  └────────────┘ ║
  ║  │              │                  │                             ║
  ╚══╬══════════════╬═════════════...══╬═════════════════════════════╝
     │              │                  │
     │         ┌────┘                  └───────┐
     │         │                               │
     │         │                               │
   ╔═╬═════════╬═══════════════════════════...═╬═══════════════════════════════╗
   ║ │         │                               │                               ║
   ║ ▼───────┐ ▼─────────────────────────┐     ▼─────────────┐ ┌─────────────┐ ║
   ║ │Event 1│ │         Event 2         │     │   Event N   │ │░░░░free░░░░░│ ║
   ║ │payload│ │         payload         │     │   payload   │ │░░░░space░░░░│ ║
   ║ └───────┘ └─────────────────────────┘     └─────────────┘ └─────────────┘ ║
   ║                                                                           ║
   ╚═Payload buffer════════════════════════...═════════════════════════════════╝
```

Although there are two different ring buffers in this system -- the descriptor
array and payload buffer -- we call the entire combined data structure an
"event ring."

A few properties about the style of communication chosen:

- It supports _broadcast_ semantics: multiple readers may read from the event
  ring simultaneously, and each reader maintains its own iterator position
  within the ring

- As in typical broadcast protocols, the writer is not aware of the readers --
  events are written regardless of whether anyone is reading them or not. This
  implies that the writer cannot wait for a reader if it is slow. Readers must
  iterate through events quickly, or they will be lost: descriptor and payload
  memory can be overwritten by later events. Conceptually the event sequence
  is a *queue* (it has FIFO semantics) but is it called a *ring* to emphasize
  its overwrite-upon-overflow semantics

- A sequence number is included in the event descriptor to detect gaps (missing
  events due to slow readers), and a similar strategy is used to detect when
  payload buffer contents are overwritten

#### An example event and payload

One particularly important event is the "start of transaction" event, which is
recorded shortly after a new transaction is decoded by the EVM. It contains the
transaction information (encoded as a C structure) as its event payload. The
payload structure is defined in `exec_event_ctypes.h` as:

```c
/// Event recorded when transaction processing starts
struct monad_exec_txn_start {
    uint64_t ingest_epoch_nanos;  ///< Epoch nanos before sender recovery
    monad_c_bytes32 txn_hash;     ///< Keccak hash of transaction RLP
    monad_c_address sender;       ///< Recovered sender address
    struct monad_c_eth_txn_header
        txn_header;               ///< Transaction header
};
```

The nested `monad_c_eth_txn_header` structure contains most of the interesting
information -- it is defined in `eth_ctypes.h` as follows:

```c
/// Fields of an Ethereum transaction, except for the variably-sized fields
/// (`data` field, EIP-2930 access list, etc.).
///
/// This type contains the fixed-size fields present in any transaction type. If
/// a transaction type does not support a particular field, it will be zero-
/// initialized.
struct monad_c_eth_txn_header {
    enum monad_c_transaction_type
        txn_type;                       ///< EIP-2718 transaction type
    monad_c_uint256_ne chain_id;        ///< T_c: EIP-155 blockchain identifier
    uint64_t nonce;                     ///< T_n: num txns sent by this sender
    uint64_t gas_limit;                 ///< T_g: max usable gas (upfront xfer)
    monad_c_uint256_ne max_fee_per_gas; ///< T_m in EIP-1559 txns or T_p (gasPrice)
    monad_c_uint256_ne
        max_priority_fee_per_gas;       ///< T_f in EIP-1559 txns, 0 otherwise
    monad_c_uint256_ne value;           ///< T_v: wei xfered or contract endowment
    monad_c_address to;                 ///< T_t: recipient or 0 (create contract)
    monad_c_uint256_ne r;               ///< T_r: r value of ECDSA signature
    monad_c_uint256_ne s;               ///< T_s: s value of ECDSA signature
    bool y_parity;                      ///< Signature Y parity (see YP App. F)
    uint32_t data_length;               ///< Length of trailing `data` array
    uint32_t access_list_count;         ///< # of EIP-2930 AccessList entries
};
```

The transaction's variably-size `data` byte array, whose length is specified
by the `data_length` field, is also part of the event payload and immediately
follows this structure. The formal nomenclature in the comments (e.g., `T_n`
and `T_c`) are references to variable names in the Ethereum Yellow Paper.

The above structure is the event payload. Some properties of the event are
recorded directly in the event descriptor instead. An event descriptor has
this format:

```c
struct monad_event_descriptor
{
    alignas(64) uint64_t seqno;  ///< Sequence number, for gap/liveness check
    uint16_t event_type;         ///< What kind of event this is
    uint16_t : 16;               ///< Unused tail padding
    uint32_t payload_size;       ///< Size of event payload
    uint64_t record_epoch_nanos; ///< Time event was recorded
    uint64_t payload_buf_offset; ///< Unwrapped offset of payload in p. buf
    uint64_t user[4];            ///< Meaning defined by the writer
};
```

For a "start of transaction" event, the `event_type` field will be set to the
value of the C enumeration constant `MONAD_EXEC_TXN_START`, a value in
`enum monad_exec_event_type`. This tells the user that it is appropriate to
cast the `const uint8_t *` pointing to the start of the event payload to a
`const struct monad_event_txn_start *`.

All the C enumeration constants start with a `MONAD_EXEC_` prefix, but
typically the documentation refers to event types without the prefix, e.g.,
`TXN_START`.

Note that the transaction number is not included in the payload structure.
Because of their importance in the monad blockchain protocol, transaction
numbers are encoded directly in the event descriptor (this is described
later in the documentation, when we discuss "flow tags").

#### Event ring files and types

Event rings are made up of four shared memory segments. Two of these -- the
event descriptor array and payload buffer -- were described earlier. The
third shared memory segment contains a header that describes metadata about
the event ring. The fourth (the "context area") is a special feature that is
not needed for execution events.

The shared memory segments are mapped into a process' address space using
[mmap(2)](https://man7.org/linux/man-pages/man2/mmap.2.html). This suggests
that the event ring's data structures live in a file somewhere, and that
shared access to it is obtained by creating shared mappings of that file.

Most of the time an event ring is a regular file, resident on a specialized
in-memory file system called
[hugetlbfs](https://lwn.net/Articles/375096/). `hugetlbfs` is similar to the
[tmpfs](https://man7.org/linux/man-pages/man5/tmpfs.5.html) in-memory
filesystem, but supports the creation of files backed by large page sizes.
The use of large pages is just an
[optimization](https://lwn.net/Articles/374424/): event ring files may be
created on any file system. If the execution daemon is told to create an
event ring file on a filesystem without hugetlb mmap support, it will log a
performance warning but will still create the file.

The event ring file format is simple: all four sections are laid out
sequentially and aligned to a large page boundary, and the header describes
the size of each section.

```
╔═Event ring file══╗
║ ┌──────────────┐ ║
║ │              │ ║
║ │    Header    │ ║
║ │              │ ║
║ ├──────────────┤ ║
║ │              │ ║
║ │    Event     │ ║
║ │  Descriptor  │ ║
║ │    Array     │ ║
║ │              │ ║
║ ├──────────────┤ ║
║ │              │ ║
║ │              │ ║
║ │              │ ║
║ │              │ ║
║ │   Payload    │ ║
║ │    Buffer    │ ║
║ │              │ ║
║ │              │ ║
║ │              │ ║
║ │              │ ║
║ │              │ ║
║ ├──────────────┤ ║
║ │              │ ║
║ │   Context    │ ║
║ │     Area     │ ║
║ │              │ ║
║ └──────────────┘ ║
╚══════════════════╝
```

The descriptor array is a just an array of `struct monad_event_descriptor`
objects, and the payload buffer is a flat byte array (of type `uint8_t[]`).
The header structure is defined this way:

```c
/// Event ring shared memory files start with this header structure
struct monad_event_ring_header
{
    char magic[6];                           ///< 'RINGvv', vv = version number
    enum monad_event_ring_type type;         ///< Kind of event ring this is
    uint8_t metadata_hash[32];               ///< Check that event types match
    struct monad_event_ring_size size;       ///< Size of following structures
    struct monad_event_ring_control control; ///< Tracks ring's state/status
};
```

The `type` field is needed because there is more than one kind of event ring:
the standard execution events are recorded to one kind of event ring, and the
performance tracer (which has more overhead, and can be turned off) is a
separate event ring. The event ring type describes what kinds of events are
present in the file:

```c
enum monad_event_ring_type : uint16_t
{
    MONAD_EVENT_RING_TYPE_NONE,  ///< An invalid value
    MONAD_EVENT_RING_TYPE_TEST,  ///< Used in simple automated tests
    MONAD_EVENT_RING_TYPE_EXEC,  ///< Core execution events
    MONAD_EVENT_RING_TYPE_PERF,  ///< Performance tracer events
    MONAD_EVENT_RING_TYPE_COUNT  ///< Total number of known event rings
};
```

This is the reason why the `event_type` field in the descriptor is the generic
integer type `uint16_t` instead of `enum monad_exec_event_type`: the event
ring itself is a generic broadcast utility, and execution events are only one
type of ring.

#### Event ring metadata hash

The `metadata_hash` field in the header is used to check for binary
compatibility between event readers and writers.

Suppose that a user compiles their application with a particular version
of `exec_event_ctypes.h`, the file which defines the execution event payloads.
Now imagine that some time later, the user deploys a new version of the
`monad` execution daemon, which has changed `exec_event_ctypes.h`, causing
the memory representation of the event payloads to be different.

If the reader does not remember to recompile their application, it could
misinterpret the bytes in the event payloads, thinking they have the old
layout from their compile-time version of `exec_event_ctypes.h`. To prevent
these kinds of errors, the binary layout of all event payloads is summarized
by a hash value which changes any time a change is made to any event payload
for that ring type. If the hash inside `exec_event_ctypes_metadata.c` does not
match the hash in the file header, the binary formats are incompatible.

A helper function called `monad_event_ring_check_type` is used to check that
an event ring file has both the expected type, and the expected payload binary
schema hash for that type. Here is an example of it being called in the
`eventwatch.c` sample program:

```c
struct monad_event_ring *exec_ring = /* initialization not shown */

if (monad_event_ring_check_type(
        &exec_ring,
        MONAD_EVENT_RING_TYPE_EXEC,
        g_monad_exec_event_metadata_hash) != 0) {
    goto Error;
}
```

If the type of event ring is not `MONAD_EVENT_RING_TYPE_EXEC` or if the
`metadata_hash` in the header does not match the value contained in the global
array `uint8_t g_monad_exec_event_metadata_hash[32]`, this function will
return the `errno(3)` domain code `EPROTO`.

## Client API overview

### Core concepts

There are two central objects in the reader API. They are:

1. __struct monad_event_ring__ - represents an event ring whose shared memory
   segments have been mapped into the address space of the current process;
   the primary thing the client does with this object is use it to initialize
   iterators that point into the event ring, using the
   `monad_event_ring_init_iterator` function
2. __struct monad_event_iterator__ - the star of the show: this iterator
   object is used to sequentially read events. The iterator's `try_next`
   operation copies the next available event descriptor (if it is available)
   and if successful, advances the iterator. It offers both zero-copy and
   memcpy style APIs for reading event payloads (zero copy APIs are
   explained in detail later in the documentation)

The easiest way to understand the API is to compile and run the included
`eventwatch` example program. This program dumps ASCII representations of
execution events to `stdout`, as they are written by a `monad` execution
daemon running on the same host.

The event descriptors are fully decoded, but the event payloads are only shown
in hexdump form, because this simple program that does not include
pretty-printing logic for all event payload types. The program is less than 250
lines of code, and reading through it should explain how the various API calls
fit together.

### Using the API in your project

`libmonad_event` is designed for third party integration, so it does not have
any library dependencies aside from a recent version of glibc. This also means
it has no dependency on the rest of the monad repository or on its build
system: the sole requirement is a C compiler supporting C23.

The `CMakeLists.txt` file in the `libs/event` directory can be used as a
top-level CMake project to build only `libmonad_event.a`. Alternatively, the
source files that make up the library target can be copied into your own
codebase. A Rust client library is also available, in another repository.

### Event ring APIs

API | Purpose
--- | -------
`monad_event_ring_mmap`           | Given a file descriptor to an event ring file, map its shared memory segments into the current process, initializing a `struct monad_event_ring`
`monad_event_ring_init_iterator`  | Given a pointer to a `struct monad_event_ring`, initialize an iterator that can be used to read from the event stream
`monad_event_ring_try_copy`       | Given a specific sequence number, try to copy the event descriptor for it, if it hasn't been overwritten
`monad_event_ring_payload_peek`   | Get a zero-copy pointer to an event payload
`monad_event_ring_payload_check`  | Check if an event payload refered to by a zero-copy pointer has been overwritten
`monad_event_ring_memcpy`         | `memcpy` the event payload to a buffer, succeeding only if the payload copy is valid
`monad_event_ring_get_last_error` | Return a human-readable string describing the last error that occured on this thread

All functions which fail return an `errno(3)` domain error code diagnosing
the reason for failure. The function `monad_event_ring_get_last_error` can
be called to provide a human-readable string explanation of what failed.

### Event iterator APIs

API | Purpose
--- | -------
`monad_event_iterator_try_next`     | If the next event descriptor if is available, copy it and advance the iterator
`monad_event_iterator_reset`        | Reset the iterator to point to the most recently produced event descriptor; used for gap recovery
`monad_exec_iter_consensus_prev`    | Rewinds an iterator to the previous consensus event (`BLOCK_START`, `BLOCK_QC`, `BLOCK_FINALIZED`, or `BLOCK_VERIFIED`
`monad_exec_iter_block_number_prev` | Rewinds an iterator to the previous consensus event for the given block number
`monad_exec_iter_block_id_prev`     | Rewinds an iterator to the previous consensus event for the given block ID

### Library organization

Core files in `libmonad_event`:

File | Contains
---- | ----
`event_ring.{h,c}` | Definitions of core shared memory structures for event rings, and the API that initializes and mmaps event ring files
`event_iterator.h` | Defines the basic event iterator object and its API
`event_iterator_inline.h` | Definitions of the `event_iterator.h` functions, all of which are inlined for performance reasons
`event_metadata.h` | Structures that describe event metadata (string names of events, descriptions of events, etc.)
`base_ctypes.h` | Definitions of basic vocabulary types common in Ethereum data (e.g., 256 bit integer types, etc).
`eth_ctypes.h` | Definitions of structures specified by the Category Labs implementationr of the Ethereum virtual machine
`exec_event_ctypes.h` | Definition of execution event payload structures, and event type enumeration `enum monad_exec_event_type`
`exec_event_ctypes_metadata.c` | Defines static metadata about execution events, and the metadata hash value array
`exec_iter_help.h` | API for rewinding the the iterator to point to block executions or consensus events

Supporting files in `libmonad_event`:

`event_ring_util.{h,c}` | API of convenience functions that are useful in most event ring programs, but which are not part of the core API
`format_err.{h,c}` | Helper utility from the `monad` codebase used to implement the `monad_event_ring_get_last_error()` function
`srcloc.h` | Helper utility used with the `format_err.h` API, for capturing source code locations in C

Other files in the SDK:

File | Contents
---- | --------
`example/eventwatch.c` | A sample program that shows how to use the API

## Event descriptors in detail

### Binary format

The event descriptor is defined this way:

```c
struct monad_event_descriptor
{
    alignas(64) uint64_t seqno;  ///< Sequence number, for gap/liveness check
    uint16_t event_type;         ///< What kind of event this is
    uint16_t : 16;               ///< Unused tail padding
    uint32_t payload_size;       ///< Size of event payload
    uint64_t record_epoch_nanos; ///< Time event was recorded
    uint64_t payload_buf_offset; ///< Unwrapped offset of payload in p. buf
    uint64_t user[4];            ///< Meaning defined by the writer
};
```

### Flow tags: the `user` fields in execution event rings

As mentioned earlier, there are different kinds of event rings used for
publishing different kinds of broadcast data. Execution event rings -- those
whose `type` field in the file header contains the enumeration constant value
`MONAD_EVENT_RING_TYPE_EXEC` -- are just one kind of ring, namely the kind
used to broadcast EVM notifications.

For each kind of ring type, we may want to publish additional data directly in
the event descriptor, e.g., if that data is common to every payload type or if
it would help the reader quickly filter out events they are not interested in,
without needing to examine the event payload. This additional data is stored
in the `user` array, and its meaning is defined by the type of event ring it
lives in.

For execution event rings, the first three values of the `user` array are
sometimes filled in. The value at each index in the array has the semantic
meaning described by the following enumeration type, which is defined in
`exec_event_ctypes.h`:

```c
/// Stored in event descriptor's `user` array to tag the block & transaction
/// context of event
enum monad_exec_flow_type : uint8_t
{
    MONAD_FLOW_BLOCK_SEQNO = 0,
    MONAD_FLOW_TXN_ID = 1,
    MONAD_FLOW_ACCOUNT_INDEX = 2,
};
```

So for example, if we have an event descriptor

```c
struct monad_event_descriptor event;
```

And its contents are initialized by a call to `monad_event_iterator_try_next`,
then `event.user[MONAD_FLOW_TXN_ID]` will contains the "transaction ID" for
that event. The transaction ID is equal to the transaction index plus one; it
is zero if the event has no associated transaction (e.g., the start of a new
block).

The idea behind the "flow" tags is that they tag events with the context they
belong to. For example, when a transaction accesses a particular account
storage key, a `STORAGE_ACCESS` event is emitted.

By looking at the `user` array for the `STORAGE_ACCESS` event descriptor, the
reader can tell it is a storage access made (1) by the transaction with index
`event.user[MONAD_FLOW_TXN_ID] - 1` and (2) to the account with index
`event.user[MONAD_FLOW_ACCOUNT_INDEX]` (this index is related to an earlier
`ACCOUNT_ACCESS` event series that has already been seen).

Flow tags are used for two reasons:

1. **Fast filtering** - if we are processing 10,000 transactions per second,
   and there are at least a dozen events per transaction, then we only have
   about 10 microseconds to process each event or we'll eventually fall behind
   and gap. At timescales like these, even touching the memory containing the
   event payload is expensive, on a relative basis. The event payload lives on
   a different cache line -- one that is not yet warm in the reader's CPU --
   and the cache line ownership must first be changed in the cache coherence
   protocol (because it was recently exclusively owned by the writer, and now
   must be shared with the reading CPU, causing cross-CPU bus traffic). For
   most applications, the user can identify transactions IDs they are
   interested in at the time of the `TXN_START` event, and then any event
   without an interesting ID can be ignored. Because the IDs are a dense
   set of integers, a simple array of type `bool[TXN_COUNT + 1]` can be
   used to efficiently look up whether subsequent events associated with that
   transaction are interesting (this can be made even more efficient using
   a single bit instead of a full `bool` per transaction)

2. **Compression** - the account of a `STORAGE_ACCESS` is referred to by an
   index (which refers to an earlier `ACCOUNT_ACCESS` event) because an
   account address is 20 bytes: large enough that it cannot fit in the two
   remaining `user` array slots

The compression technique is also used for storing the block associated with
an event, in `event.user[MONAD_FLOW_BLOCK_SEQNO]`. The flow tag in this case
is the _sequence number_ of the `BLOCK_START` event that started the
associated block. A few things to note about this flow tag:

- Sometimes it is zero (an invalid sequence number), which means the event
  is not associated with any block; although most events are scoped to a
  block, the consensus state change events (`BLOCK_QC`, `BLOCK_FINALIZED`,
  and `BLOCK_VERIFIED`) do not occur inside a block

- Note that the block flow tag is _not_ the block number. This is because
  at the time events are seen, the consensus algorithm has not finished
  voting on whether or not the block will be included in the canonical block
  chain (this is discussed extensively in the next section). Until a block
  becomes finalized, the only unambiguous way to refer to it is by its unique
  ID, which is 32 bytes long hash value (which can be read from the
  `BLOCK_START` payload); thus the block flow tag is also a form of
  compression

- Having the sequence number allows us to rewind the iterator to the start
  of the block, if we start observing the event sequence in the middle of
  a block (e.g., if the reader starts up after the execution daemon). An
  example of this (and a detailed explanation of it) can be found in the
  `eventwatch.c` example program, in the `find_initial_iteration_point`
  function

## Consensus states

### _Beware_: the events you see may not actually happen!

Execution events are "trace" information reported directly from the EVM. As
with legacy Ethereum, execution and consensus are decoupled -- they are
different programs running different algorithms. Consensus is the algorithm
which decides whether or not a potential block will become part of the
blockchain.

Monad has considerably more "parallelism" in its fundamental design than
legacy Ethereum does: consensus is allowed to run in parallel with execution,
and can vote on a block even before that block has finished executing.[^1]

Typically though, _block execution will finish before the consensus algorithm
does_. This means that you will find out _sometime later_, whether the block
and its transactions (and their state effects) were actually committed to the
Monad blockchain or not.

The fundamental reason why consensus is slower is that it is a distributed
algorithm that needs to run over the public Internet. Several back-and-forth
exchanges are needed, and these must reach data centers all over the world,
while being robust to real-world network latency issues. For this reason,
consensus rounds are approximately 500 milliseconds long. In the typical
case, it takes two of these 0.5 second time slices to finalize a block.

Thus when you see an execution event, you're probably seeing it ~1 second
before consensus will decided whether or not to append the associated block to
the blockchain (although half-way through, you will receive a notification
that most of risk of reversion has been removed).

So you should be aware of two things:

The events you see are describing what the effects and outputs of transactions
_will_ be, but _only if_ the block ends up getting finalized on the Monad
blockchain. You will find out if that happens later, via a few special event
types. Despite being "execution events", these ultimately come from the
consensus software, and explicitly communicate what consensus decided to do
with the block, after you have already seen the events created by that block's
execution.

[1]: If you are wondering how this is possible, it's because a block whose
format is correct (consists of only valid transactions and obeys all the
protocol rules) is guaranteed to execute and eventually halt in the EVM.
It is possible to perform this validation _without_ actually executing the
transactions and computing the final state effects of the block.

### Proposed blocks, block tags, and consensus events

The API documentation for the `struct monad_exec_block_tag` explains the
basics:

> Once a block is canonically appended to the block chain, it becomes uniquely
> identified by a (sequentially increasing) block number, also called a "block
> height." The inclusion of a block on the blockchain is the goal of the
> consensus algorithm, and is called "finalization."
>
> When a block it first constructed, it is constructed assuming it will become
> the next block number, `B`. Prior to finalization, consensus nodes are still
> trying to agree whether or not this candidate block will become block `B`.
>
> During this time, multiple blocks could be proposed, some of which are
> competing candidates to become the same block number `B`. For performance
> reasons, the execution daemon is allowed to speculatively execute blocks in
> the EVM before they finalize in consensus. Consequently, even blocks that
> never become part of the blockchain may produce execution events; execution
> events may describe transactions that "never happen" on chain.
>
> Thus, when a block number is seen during an event, e.g., `BLOCK_START`, it
> is not necessarily the case that the corresponding block will be added to
> the blockchain as this block number (or at all).
>
> The information in the "tag" object is used to track a block as it is
> operated on by the consensus algorithm. The (not yet unique) `block_number`
> is the number the block _will_ have, if it eventually gets finalized. The
> `id` field uniquely identifies the block contents, vs. all the other
> proposals of different blocks to become the same `block_number`. `id` can be
> used to track this specific block before finalization.

The above documentation is describing the following structure:

```
struct monad_exec_block_tag
{
    monad_c_bytes32 id;    ///< Monad consensus unique ID for block
    uint64_t block_number; ///< Proposal is to become this block
};
```

These "block tags" appear in three kinds of event payloads, corresponding
to the first three phases of the consensus protocol.

#### First consensus event: **`BLOCK_START`**

```c
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
```

When a new block is proposed by a leader (a Monad validator node), it is sent
to all consensus nodes to be voted on. If the block is valid (i.e., follows
all protocol rules), the consensus node will vote "yes" for it, and schedule
it for speculative execution immediately. Shortly after this happens --
even as the "yes" vote is starting to be transmitted over the Internet --
the execution daemon begins executing the proposed block in the EVM.

The first event recorded by the EVM is a `BLOCK_START` event, whose event
payload contains a `block_tag` field that introduces the unique ID for the
block and the block number it will have, if it gets voted in. Almost all
execution events (transaction logs, call frames, receipts, etc.) occur between
the `BLOCK_START` and `BLOCK_END` events. In the current implementation, block
execution is never pipelined, so all events between `BLOCK_START` and
`BLOCK_END` are for a single block, and there will not be another
`BLOCK_START` until the current block is ended.

Unlike the other events in this list, `BLOCK_START` is both a "consensus
event" (and it means consensus has received the proposal) and an "EVM event,"
meaning that execution information is being made available to you. The other
events in this list are pure consensus events: they tell you what happens
to the proposed block in the consesus algorithm, after you've already seen
its EVM events.

#### Second consensus event: **`BLOCK_QC`**

```c
/// Event recorded when a proposed block obtains a quorum certificate
struct monad_exec_block_qc
{
    struct monad_exec_block_tag
        block_tag;              ///< QC for proposal with this block
    uint64_t round;             ///< Round of proposal vote
    uint64_t epoch;             ///< Epoch of proposal vote
};
```

In parallel with a proposed block being executed, the consensus algorithm is
conducting a first round vote on whether or not that block will be appended
to the blockchain. The goal of this referendum is to produce a "quorum"
(minimum number of required votes for referendum to pass) of "yes" votes.

The vote is conducted by gathering cryptographic signatures, and when a
quorum of nodes sign a "yes" vote, their aggregate signature is called a
"quorum certificate." Having a quorum certificate means that the proposal has
passed the first round of voting. When this happens, a `BLOCK_QC` event will
be recorded with the same `block_tag` as was present in the `BLOCK_START`
payload, when the proposed block was speculative executed earlier.

A few things to note about `BLOCK_QC`:

##### A block might never get a QC

A proposed block might never receive a QC, if its consensus vote fails. When
you see `BLOCK_START` (and all subsequent EVM events), the only thing you know
is that the local node has voted "yes", but it remains to be seen whether
enough other nodes will agree or not.

The most common reason that a block does not get voted in is network latency
issues. Suppose, for example, that both your node and the leader are in
Australia, and there is significant congestion with the cross-continental
network traffic. In that case, most of the blockchain nodes may not learn
about the proposal before the timeout period expires, and the vote will fail.

##### For some block number `B`, _some_ proposed block will get a QC

If you do not receive a `BLOCK_QC` for a particular block with block number
`B`, then at some other time you will receive a different proposed block for
`B`. That is, you'll see a different `BLOCK_START` (where
`block_tag.block_number` is also `B`, but `block_tag.id` is different). This
will be followed by all of the new block's EVM events, followed eventually
by a `BLOCK_QC` for this new block.

##### QC does not mean it's on the blockchain

A block does _not_ become canonically appended to the blockchain when it
receives a QC. Monad's consensus algorithm uses two rounds of voting, and
each round reduces the risk that a proposed block can be reverted. In the
current iteration of the algorithm, having a QC (first round vote) removes
the most common kinds of risks, but some risk of being reverted remains until
a second round of voting occurs. If the second round vote is successful, only
then will the block become "finalized" (which is discussed next).

Having a QC removes the risk that a block will be "lost" to the most common
issues such as network outages and latency issues. If network problems occur
after QC a received, i.e., if the second round of voting is disrupted, the
algorithm will continue conducting the second round vote until enough of the
network is restored for the vote to succeed.

How can a block with a QC still be reverted then? It can happen if the leader
of the second round vote is malicious and wants to rig the vote, causing the
second round of voting to fail. Blockchains employ various schemes to prevent
this from occurring too frequently, but it is a fundamental issue that is
faced by all BFT consensus algorithms.

#### Third consensus event: **`BLOCK_FINALIZED`**

```c
/// Event recorded when consensus finalizes a block
typedef struct monad_exec_block_tag monad_exec_block_finalized;
```

The finalized event payload does not have any information that isn't already
part of the block tag, so the payload is just the tag of the block that gets
finalized.

When a block with height `B` is finalized, it _implicitly_ abandons all
other proposed blocks with the same block height `B`. Such blocks could be
in either the proposed or the QC state. We say the abandonment is implicit
because no event will be recorded to explicitly announce the abandonment of
previous seen block tag.

If the reader has been tracking some state associated with unfinalized blocks,
then upon every `BLOCK_FINALIZED` event, that read must check for any blocks
(1) with the same block number, but (2) with a different ID, and discard the
state of those blocks. Those blocks will never be appened to the blockchain
and the associated transactions and their effects will never occur.

#### Fourth consensus event: **`BLOCK_VERIFIED`**

```c
/// Event recorded when consensus verifies the state root of a finalized block
struct monad_exec_block_verified
{
    uint64_t block_number; ///< Number of verified block
};
```

The consensus algorithm produces one last event for a block, called
`BLOCK_VERIFIED`. This time it is sufficient to identify the block only by its
block number. Now that the block is finalized, it becomes the canonical block
with that number and cannot be reverted without a hard fork. Thus, we no
longer need the block tag.

The verified state is a consequence of Monad's parallelized execution. Recall
that a consensus node votes on a block _before_ its execution is complete.
This implies that consensus must be voting on the block's execution inputs,
but _not_ on the block's execution outputs.

Consensus nodes cannot be voting, for example, on the correct value of the
state root produced by the execution of the block, because they don't know
what it is (remember, it is being computed in parallel with the vote
occuring). This means that an event such as `BLOCK_QC` does not certify the
correctness of any output fields in the Ethereum block header such as
`state_root`, `receipts_root`, etc.

This is possible because any well-formed Ethereum block will have completely
deterministic effects on the blockchain state, when executed by a conforming
EVM implementation. Thus it is safe to append a block onto the blockchain,
knowing that everyone will agree on its behavior, even if we don't know
exactly what the behavior will be.

Clearly though, for the blockchain to be reliable, consensus nodes _must_
eventually vote on the correctness of the executon outputs. Suppose they did
not, and further suppose that a bug existed in some execution nodes but not
in others (perhaps running a different version of the client software). If
there were no mechanism to feed the execution outputs back into consensus
decisions, the state could become forked without anyone noticing. Consensus
proposals _start_ by assuming that all execution nodes will compute the
correct state, but to prevent bugs and malicious actions from compromising
the network, it must check that this happens eventually.

Here is how Monad solves this issue:

To give execution ample time to finish, execution outputs for block `B`
are not incorporated into the consensus protocol until three rounds in the
future, alongside the proposal of block `B+3`. When _this_ proposal is
finalized (ideally two rounds later, during the proposal of block `B+5`),
then a supermajority of nodes will have voted for the correct values of
the execution outputs.

To understand more, read [here](https://docs.monad.xyz/monad-arch/consensus/asynchronous-execution).

To roughly summarize the difference:

- `BLOCK_FINALIZED` means the block's definition (i.e., its transactions) are definitely part of the block chain
- `BLOCK_VERIFIED` means that a supermajority stake's worth of other nodes have verified that your local node's computation of the state changes of these transactions match the same values as the supermajority's

## Advanced topics

### When are events published?

Execution events are recorded roughly "as they are happening" inside the
execution daemon: you see a `BLOCK_START` event at roughly the same moment
that the execution daemon beings processing a new block, followed by the
start of the first transaction (a `TXN_START` event) about 1 millisecond
later. Most transaction-related events are recorded less than one
microsecond after the transaction they describe has completed.

Each significant action that happens within the EVM generates a separate
event. For example, if a transaction emits three logs, there will be three
`TXN_LOG` events, rather than a single event containing an array of size 3.
The reader sees every granular EVM action that occurs in a transaction (logs,
call frames, state reads and writes) as a new event.

Execution of a typical transaction will emit a few dozen events, but large
transaction can be emit hundreds of events. The `TXN_EVM_OUTPUT` event --
which is recorded as soon as the transaction is finished -- provides a summary
accounting of how many more events related to that transaction will follow
(how many logs, how many call frames, etc.), so that any memory can be
preallocated. Such an event is referred as a "header event" in the
documentation: an event whose content describes the number of subsequent,
related events that will be recorded.

All these events are recorded as soon as the transaction is "committed" to the
currently-executing block. This happens before the block has finished
executing, and should not be confused with the unrelated notion of "commitment"
in the consensus algorithm. Although there are complex speculative execution
optimizations inside the execution daemon, the recording of a transaction takes
place when all work on a particular transaction has finished. This is referred
to as "transaction commit" time.

This is a different than the block-at-a-time style update you would see in,
for example, the Geth real time events WebSocket protocol (which our RPC server
also supports). Certain properties of the block (its hash, its state root,
etc.) are not known at the time you see the transactions. If you would like
block-at-a-time updates, the Rust SDK contains a utility called `BlockBuilder`,
which will aggregate the events back into larger, block-oriented updates.

One thing to be careful of: although transactions are always committed to a
block in index order, they might be recorded out of order. That is, you must
assume that the set of events that make up transactions 2 and 3 could be "mixed
together" in any order. This is because of optimizations in the event recording
code path.

### Sequence numbers and the lifetime detection algorithm

All event descriptors are tagged with an incrementing sequence number
starting at 1. Sequence numbers are 64-bit unsigned integers which do not
repeat unless the execution daemon is restarted. Zero is not valid sequence
number.

Also note that the sequence number modulo the descriptor array size equals
the array index where the *next* event descriptor will be located. This is
shown below with a concrete example where the descriptor array size is 64.
Note that the last valid index in the array is 63, then access wraps around
to the beginning of the array at index 0.

```
                                                         ◇
                                                         │
  ╔═...═════════════════════════Event descriptor array═══╬═══════════════════...═╗
  ║                                                      │                       ║
  ║     ┌─Event────────┐┌─Event────────┐┌─Event────────┐ │ ┌─Event─────────┐     ║
  ║     │              ││              ││              │ │ │               │     ║
  ║     │ seqnum = 318 ││ seqnum = 319 ││ seqnum = 320 │ │ │ seqnum = 256  │     ║
  ║     │              ││              ││              │ │ │               │     ║
  ║     └──────────────┘└──▲───────────┘└──────────────┘ │ └───────────────┘     ║
  ║            61          │   62              63        │         0             ║
  ╚═...════════════════════╬═════════════════════════════╬═══════════════════...═╝
                           │                             │
                           ■                             ◇
                           Next event                    Ring buffer
                                                         wrap-around to
      ┌──────────────────────────────┐                   zero is here
      │last read sequence number     │
      │(last_seqno) is initially 318 │
      └──────────────────────────────┘
```

In this example:

- We keep track of the "last seen sequence number" (`last_seqno`) which has
  value `318` to start; being the "last" sequence number means we have already
  finished reading the event with this sequence number, which lives at array
  index `61`

- `318 % 64` is `62`, so we will find the potential next event at that index
  *if* it has been produced

- Observe that the sequence number of the item at index `62` is `319`, which
  is the last seen sequence number plus 1 (`319 == 318 + 1`). This means that
  event `319` has been produced, and its data can be safely read from that
  slot

- When we're ready to advance to the next event, the last seen sequence
  number will be incremented to `319`. As before, we can find the *next*
  event (if it has been produced) at `319 % 64 == 63`. The event at this
  index bears the sequence number `320`, which is again the last seen
  sequence number + 1, therefore this event is also valid

- When advancing a second time, we increment the last seen sequence number
  to `320`. This time, the event at index `320 % 64 == 0` is *not* `321`,
  but is a smaller number, `256`. This means the next event has not been
  written yet, and we are seeing an older event in the same slot. We've
  seen all of the currently available events, and will need to check again
  later once a new event is written

- Alternatively we might have seen a much larger sequence number, like
  `384` (`320 + 64`). This would mean that we consumed events too slowly, so
  slowly that the 63 events in the range `[321, 384)` were produced in the
  meantime. These were subsequently overwritten, and are now lost. They can
  be replayed using services external to event ring API, but _within_ the
  event ring API itself there is no way to recover them

### Lifetime of an event payload, zero copy vs. memcpy APIs

Because of the descriptor overwrite behavior, an event descriptor might be
overwritten by the `monad` process while a reader is still examining its
data. To deal with this, the reader API makes a copy of the event descriptor.
If it detects that the event descriptor changed during the copy operation, it
reports a gap. Copying an event descriptor is fast, because it is only a
single cache line in size.

This is not the case for event payloads, which could potentially be very
large. This means a `memcpy(3)` of an event payload could be expensive, and
it would be advantageous to read the payload bytes directly from the payload
buffer's shared memory segment: a "zero-copy" API. This exposes the user to
the possibility that the event payload could be overwritten while still
using it, so two solutions are provided:

1. A simple detection mechanism allows payload overwrite to be detected at
   any time: the writer keeps track of the minimum payload offset value
   (_before_ modular arithmetic is applied) that is still valid. If the
   offset value in the event descriptor is smaller than this, it is no
   longer safe to read the event payload

2. A payload `memcpy`-style API is also provided. This uses the detection
   mechanism above in the following way: first, the payload is copied to
   a user-provided buffer. Before returning, it checks if the lifetime
   remained valid after the copy finished. If so, then an overwrite did not
   occur during the copy, so the copy must be valid. Otherwise, the copy is
   invalid

The reason to prefer the zero-copy APIs is that they do less work. The
reason to prefer memcpy APIs is that it is not always easy (or possible) to
"undo" the work you did if you find out later that the event payload was
corrupted by an overwrite while you were working with it. The most logical
thing to do in that case is start by copying the data to stable location,
and if the copy isn't valid, to never start the operation.

An example user of the zero-copy API is the `eventwatch` example program,
which can turn events into printed strings that are sent to `stdout`. The
expensive work of formatting a hexdump of the event payload is performed
using the original payload memory. If an overwrite happened during the
string formatting, the hexdump output buffer will be wrong, but that is OK:
it will not be sent to `stdout` until the end. Once formatting is complete,
`eventwatch` checks if the payload expired and if so, writes an error to
`stderr` instead of writing the formatted buffer to `stdout`.

Whether you should copy or not depends on the characteristics of the reader,
namely how easily it can deal with "aborting" processing.
