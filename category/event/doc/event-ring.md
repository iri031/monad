# Event rings in detail

## Event ring files and types

Event rings are made up of four shared memory segments. Two of these -- the
event descriptor array and payload buffer -- are described in the
[overview documentation](overview.md). The third shared memory segment
contains a header that describes metadata about the event ring. The fourth
(the "context area") is a special feature that is not needed for execution
events.

The shared memory segments are mapped into a process' address space using
[mmap(2)](https://man7.org/linux/man-pages/man2/mmap.2.html). This suggests
that the event ring's data structures live in a file somewhere, and that
shared access to it is obtained by creating shared mappings of that file.

Most of the time an event ring is a regular file, created on a special
in-memory file system called
[hugetlbfs](https://lwn.net/Articles/375096/). `hugetlbfs` is similar to the
[tmpfs](https://man7.org/linux/man-pages/man5/tmpfs.5.html) in-memory
filesystem, but supports the creation of files backed by large page sizes.
The use of large pages is just an
[optimization](https://lwn.net/Articles/374424/): event ring files may be
created on any file system. If the execution daemon is told to create an
event ring file on a filesystem without hugetlb mmap support, it will log a
performance warning but will still create the file.

### Specifying the event ring file

XXX

### Event ring file format

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
objects, and the payload buffer is a flat byte array (i.e., it has type
`uint8_t[]`). The header structure is defined this way:

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
separate event ring. The `type` field describes what kinds of events are
present in an event ring file:

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

This is the reason why the `event_type` field in the event descriptor is the
generic integer type `uint16_t` instead of `enum monad_exec_event_type`: the
event ring itself is a generic broadcast utility, and execution events are
only one type of ring.

### Binary schema versioning: metadata hash

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
struct monad_event_ring exec_ring;

/* initialization of `exec_ring` not shown */

if (monad_event_ring_check_type(
        &exec_ring,
        MONAD_EVENT_RING_TYPE_EXEC,
        g_monad_exec_event_metadata_hash) != 0) {
    errx(EX_SOFTWARE, "event library error -- %s",
         monad_event_ring_get_last_error());
}
```

If the type of event ring is not `MONAD_EVENT_RING_TYPE_EXEC` or if the
`metadata_hash` in the file header does not match the value contained in the
global array `uint8_t g_monad_exec_event_metadata_hash[32]`, this function
will return the `errno(3)` domain code `EPROTO`.

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
