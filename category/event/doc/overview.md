# Execution event overview

The `monad` execution daemon includes a system for recording events that occur
during transaction processing. An "execution event" is a notification that the
EVM has performed some action, such as "an account balance has been updated"
or "a new block has started executing." `monad` EVM events can be observed by
external third-party applications, using a high-performance inter-process
communication channel.

There are two parts to the execution event system:

1. The `monad` execution daemon is the *writer* of all events
2. An external application can become a *reader* of events using the C
   library `libmonad_event`, or alternatively, the Rust module
   `monad-exec-events`

The execution daemon publishes event data to shared memory, and external
applications read from this same shared memory region to observe the events.
This file provides an overview of the basic concepts used in both the C
and Rust APIs.

## Event basics

### What is an event?

Events are made up of two components:

1. The *event descriptor* is a fixed-size (currently 64 byte) object describing
   an event that has happened. It contains the event's type, a sequence number,
   a timestamp, and some internal book-keeping information.
2. The *event payload* is a variably-sized piece of extra data about the event,
   which is specific to the event type. For example, a "transaction log" event
   describes a single EVM log record emitted by a transaction. The transaction
   log's event payload contains the contract address, the log topics, and the
   log data. Some of the fields in the event descriptor not already mentioned
   are used to communicate where in shared memory the payload bytes are
   located, and the payload's length.

### Where do events live?

When an event occurs, the execution daemon inserts an event descriptor into
a ring buffer that lives in a shared memory segment. Event payloads are
stored in an array (in a separate shared memory segment) called the "payload
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

Keep in mind that real event payloads are typically much larger (in terms of
number of bytes) than the event descriptors, even though they don't appear that
way in this simple diagram. The diagram is primarily trying to show that:

- Event descriptors are _fixed-size_ and event payloads are _variably-sized_
- An event descriptor refers / "points to" the location of its payload
- Event descriptors and payloads live in different contiguous arrays of shared
  memory

Although there are two different ring buffers in this system -- the descriptor
array and payload byte buffer -- we call the entire combined data structure an
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

### An example event and its payload

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

> [!NOTE]
> If you are using the Rust SDK, a `struct` with the same name (and the same
> binary layout, via `#[repr(C)]`) is generated by
> [bindgen](https://docs.rs/bindgen/latest/bindgen/) when the `monad-exec-events`
> package is built

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

The transaction's variably-sized `data` byte array, whose length is specified
by the `data_length` field, is also part of the event payload and immediately
follows this structure. The formal nomenclature in the comments (e.g., `T_n`
and `T_c`) are references to variable names in the Ethereum Yellow Paper.

`struct monad_exec_txn_start`  is the payload for a "start of transaction"
event, but the common properties of the event are recorded directly in the
event descriptor. Most importantly, these include the numeric code that
identifies the type of event, so we know how to decode the payload in the
first place.

An event descriptor is defined this way:

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
elsewhere in the documentation, on the topic of "flow tags", which relates
to the `user` field of the descriptor).
