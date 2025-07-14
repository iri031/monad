# C API overview

## Core concepts

There are two central objects in the event reader C API. They are:

1. __struct monad_event_ring__ - represents an event ring whose shared memory
   segments have been mapped into the address space of the current process;
   the primary thing the client does with this object is use it to initialize
   iterators that point into the event ring, using the
   `monad_event_ring_init_iterator` function
2. __struct monad_event_iterator__ - the star of the show: this iterator
   object is used to read sequential events. The iterator's `try_next`
   operation copies the next available event descriptor (if it is available)
   and if successful, advances the iterator. Conceptually, it behaves like
   the expression `descriptor = *i++`, if an event descriptor is ready
   immediately (it does nothing otherwise)

The easiest way to understand the API is to compile and run the included
`eventwatch` example program. This program dumps ASCII representations of
execution events to `stdout`, as they are written by a `monad` execution
daemon running on the same host.

In `eventwatch`, the event descriptors are fully decoded, but the event
payloads are only shown in hexdump form, because this simple program that
does not include pretty-printing logic for all event payload types. The
program is less than 250 lines of code, and reading through it should explain
how the various API calls fit together.

## Using the API in your project

`libmonad_event` is designed for third party integration, so it does not have
any library dependencies aside from a recent version of glibc. This also means
it has no dependency on the rest of the monad repository or on its build
system: the sole requirement is a C compiler supporting C23.

The `CMakeLists.txt` file in the `libs/event` directory can be used as a
top-level CMake project to build only `libmonad_event.a`. Alternatively, the
source files that make up the library target can be copied into your own
codebase. A Rust client library is [also available](rust-api.md).

## Event ring APIs

API | Purpose
--- | -------
`monad_event_ring_mmap`           | Given a file descriptor to an open event ring file, map its shared memory segments into the current process, initializing a `struct monad_event_ring`
`monad_event_ring_init_iterator`  | Given a pointer to a `struct monad_event_ring`, initialize an iterator that can be used to read from the event ring
`monad_event_ring_try_copy`       | Given a specific sequence number, try to copy the event descriptor for it, if it hasn't been overwritten
`monad_event_ring_payload_peek`   | Get a zero-copy pointer to an event payload
`monad_event_ring_payload_check`  | Check if an event payload refered to by a zero-copy pointer has been overwritten
`monad_event_ring_memcpy`         | `memcpy` the event payload to a buffer, succeeding only if the payload copy is valid
`monad_event_ring_get_last_error` | Return a human-readable string describing the last error that occured on this thread

All functions which fail return an `errno(3)` domain error code diagnosing
the reason for failure. The function `monad_event_ring_get_last_error` can
be called to provide a human-readable string explanation of what failed.

## Event iterator APIs

API | Purpose
--- | -------
`monad_event_iterator_try_next`     | If the next event descriptor if is available, copy it and advance the iterator
`monad_event_iterator_try_copy`     | Copy the event descriptor at the current iteration point, without advancing the iterator
`monad_event_iterator_reset`        | Reset the iterator to point to the most recently produced event descriptor; used for gap recovery
`monad_exec_iter_consensus_prev`    | Rewinds an iterator to the previous consensus event (`BLOCK_START`, `BLOCK_QC`, `BLOCK_FINALIZED`, or `BLOCK_VERIFIED`)
`monad_exec_iter_block_number_prev` | Rewinds an iterator to the previous consensus event for the given block number
`monad_exec_iter_block_id_prev`     | Rewinds an iterator to the previous consensus event for the given block ID

## Library organization

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
