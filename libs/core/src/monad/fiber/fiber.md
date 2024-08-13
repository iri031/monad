# Design and implementation notes

## Lightweight fiber library overview

A fiber library generally consists of three parts:

1. The fibers themselves
2. The synchronization primitives needed for fibers to communicate
   with each other; without these, fibers could only yield or
   return
3. Some kind of scheduler, which makes a sleeping fiber runnable
   again when a synchronization primitive signals that a resource
   is ready, so the fiber(s) waiting for it can wake up

This code makes an effort to be much simpler than a typical fiber library,
which is often a full-fledged "frameworks." In this lightweight library,
the coupling between the three parts is minimal, and occurs in only a few
lines of code. Thus the design can be changed quickly to whatever our
internal needs are, rather than being a general purpose library.

The implementation is also meant to be clear, such that a programmer can
understand it fully without much trouble. Take this with a grain of salt
though: context-switching code can be tricky, so understanding all the
implementation details will require *some* time investment!

## Where is the code?

1. For the fibers themselves:
   - `fiber.h` - defines the interface for fibers, i.e., the public
     functions and the central `struct monad_fiber` object
   - `fiber.c` - most of the fiber implementation of `fiber.h`
   - `fiber_thr.c` - an implementation file, related to the "thread fiber"
      feature (see the **Thread Fibers** section later on)
   - `fiber_util.h` - debugging and helper utilities for fibers
   - `fiber_util.c` - implementation file for `fiber_util.h`

2. For the synchronization primitives:
   - `fiber_channel.h` - implements a "channel" synchronization primitive
     for fiber objects; for a description of channels see
     [here](https://en.wikipedia.org/wiki/Channel_(programming))
   - `fiber_semaphore.h` - implements a semaphore synchronization
     primitive for fibers
   - `fiber_sync.h` - a "wait queue" utility that is shared by the
     channel and semaphore implementation
   - `future.hpp` - defines the `simple_future<T>` and `simple_promise<T>`
     C++ types that are similar to (but less fully-featured than) those
     found in C++11 `<future>`; these are implemented in terms of
     `monad_fiber_channel_t` (for `simple_promise<T>`) and
     `monad_sempaphore_t` (for the `simple_promose<void>` specialization)

3. The "scheduler"
   - `monad_run_queue.h` - defines the interface for a simple thread-safe
     priority queue of `monad_fiber_t*` objects; 
   - `monad_run_queue.c` - implementation file for `monad_run_queue.h`

### Why is "scheduler" in quotes above?

To keep the design simple and less monolithic, the `monad_fiber` library does
not have a full-fledged scheduler, or any higher-level abstractions such as a
task pool, run-loop, worker threads, etc.

The intention is for the user code to solve its problem directly, creating
these things as (and only if!) it needs them, and using `monad_fiber` as a
bare-bones helper module. The only point of coupling between the three parts of
a fiber system is the priority queue  type, `monad_run_queue_t`.

A `monad_fiber_t` keeps track of an associated `monad_run_queue_t*`, and when
the fiber is signaled for wakeup by a synchronization primitive, it
"wakes up" by re-enqueueing the fiber back on this associated priority queue.

The library does not run anything by itself. Instead it offers a single
function (`monad_fiber_run`) to start or resume a fiber, which runs the fiber's
function until the function reaches a suspension point -- at which point
`monad_fiber_run` just returns. The library does little beyond that.

The only other "automatic" thing it does is re-enqueue the fiber on a priority
queue if a synchronization primitive wakes the fiber. The user of the library
must create their own concepts like worker threads, pools, etc. to
enqueue/dequeue fibers from a `monad_run_queue_t`, and use this library to run
them. The exact topology and way of doing this is not specified by the library.

## `monad_fiber_t` basic design

### How to use `monad_fiber_t`

A fiber is an execution resource for an ordinary function having this
function type:

```.h
typedef uintptr_t (monad_fiber_ffunc_t)(uintptr_t);
```

The fiber runs this function until the function decides to suspend itself,
either  by yielding, returning, or going to sleep on some synchronization
condition that is not met yet (e.g., waiting for a semaphore to signal).
When the fiber suspends, the current thread of execution begins executing
something else. It may later be resumed, at which point execution continues
at the point where it left off.

Most of the implementation can be understood by thinking about exactly
how and when a fiber switches. Here is the model we follow:

- A fiber is started or resumed by calling the `monad_fiber_run`
  function, passing in the `monad_fiber_t*` that the user wants to run;
  that is, the context that _calls_ `monad_fiber_run` will switch into the
  given fiber and begin (or resume) running it

- In general, when a fiber suspends for any reason (yield, sleeping,
  returning, etc.), it jumps back to the context that was executing
  previously. This is the context that was running the implementation
  of `monad_fiber_run` in the first place, so the suspension of a fiber
  appears to the caller of `monad_fiber_run` as the `monad_fiber_run`
  function returning back to them

- In general then, the function that calls `monad_fiber_run` is
  a lightweight scheduler: it decides to run fibers somehow, and
  calls `monad_fiber_run` in a loop, with the sequence of fibers it
  wishes to run

- The most obvious design is to use a single global priority queue
  (the `monad_run_queue_t` utility). Each worker takes the
  next-highest-priority item and runs it until it suspends

Here is an example

```c
XXX;
```

### Implementation notes for `monad_fiber_t`

The fiber implementation has two layers:

1. **Machine-independent layer** - this is shared by all architectures
   and addresses how the fibers transfer control between each other; most
   of this code is in `fiber.c`, but some details are in `fiber_thr.c`

2. **Machine-dependent layer** - this consists of only two functions, 
   `monad_make_fcontext` and `monad_jump_fcontext` which were imported
   from the Boost.Context third-party library. These are the original
   names of the functions, except with the `monad_` prefix added. They
   are the low-level context switch functions implemented in assembly
   language for a particular architecture, calling convention, and ABI.

#### Machine independent switching

The machine-independent part of the fiber switch is handled in two phases
(called "start switch" and "finish switch"), which happen by calling
two functions in `fiber.c`:

```.h
monad_fiber_t *monad_fiber_start_switch(monad_fiber_t *cur_fiber,
                                        monad_fiber_t *next_fiber);

monad_fiber_t* _monad_fiber_finish_switch(monad_fiber_t *cur_fiber,
                                          monad_fiber_t *prev_fiber,
                                          monad_fcontext_t prev_fiber_sctx)
```

`_monad_fiber_finish_switch` starts with an underscore to emphasize that it
is intended to be an internal function, even though it has external linkage
so that `fiber_thr.c` can call it. `monad_fiber_start_switch` has internal
linkage, and is only called inside `fiber.c`.

The suspension points (`monad_fiber_yield`, the synchronization primitive
sleep functions, and the fiber function return stub), call this
slightly-higher-level wrapper, which will suspend the current fiber and
switch to another one:

```.h
void _monad_fiber_suspend(monad_fiber_t *self,
                          enum monad_fiber_state next_state,
                          enum monad_fiber_suspend_type suspend_type,
                          uintptr_t eval)
```

Some details of how "start_switch" and "finish_switch" work:

- To perform a switch, we have a notion of the current fiber (which
  will be *switched from* and thus suspended) and a next fiber
  (which will be *switched to*, and thus resumed)

- Before the switch starts, and after the switch finishes, the
  current thread must own the spinlocks of both fibers; they
  remain locked throughout both halves of the switching process, and
  are released only when the switch completes; once the switch completes,
  the current `monad_fiber_t` object remains unlocked as it is running

- When `monad_fiber_start_switch` is called, we are running on the stack
  of the current fiber; this function performs some book-keeping and calls
  the machine-dependent switch function, which causes the switch to happen
  at the hardware level

- Immediately after the hardware-level switch happens, we are running on
  the stack of the resumed (or newly-started) fiber, and the previously
  running fiber is now suspended; this resumption site must immediately call
  `_monad_fiber_finish_switch` to complete the switch; we also have access
  to the `monad_fiber_t*` of the suspended fiber we just switched from (as
  the `prev_fiber` variable) and the machine-dependent context pointer of
  its suspension point (`prev_fiber_sctx`, where `sctx` means "suspended
  context")

- The resumption can only happen at well-defined locations: namely the start
  of the fiber, or immediately after the suspension "returns" (see the next
  point). This is the point where we must call `_monad_fiber_finish_switch`

- The tricky part of understanding how this works is becoming familiar with
  the following interesting pattern: when we perform a `monad_jump_fcontext`,
  we are suspended and control is transferred away from us. When control
  transfers back to us, it has the appearance of *returning* from the original
  jump function, which had jumped away. To understand this code at a deep
  level, I suggest working through how the lowest-level machine-dependent
  assembly jump functions work between two fibers. This will take a few hours,
  but will demystify the essential pattern: when we *return* from a jump,
  we've been resumed and are on the original stack, but are potentially on a
  different host thread than when we were suspended on (!)

## Thread fibers (or "what is `fiber_thr.c`?")

Most fibers are user-created, but in the current db implementation, an
ordinary thread of execution is sometimes treated as though it is running on
a fiber. This is an API idiom that Boost.Fiber allowed, thus the
existing db code grew to rely on it.

For this to work, we need to make an ordinary thread context pretend that it
is a fiber. This is called a "thread fiber" in the code. To simplify
`fiber.c`, most of the code for thread fiber support lives in a different
file, `fiber_thr.c`.

This is because thread fibers are special in several ways, thus they are
easy to separate out and not complicate the main implementation file.

There are two parts of thread fiber support:

1. Creating a "fake" `monad_fiber_t` that represents a thread context; this
   is what is returned if you call `monad_fiber_self()` in the context of a
   normal thread rather than in a "real" fiber

2. Creating a dummy "wakeup fiber" that the thread fiber switches to, when
   it goes to sleep on a wait channel. For performance reasons, the wakeup
   fiber spins until it is woken up

