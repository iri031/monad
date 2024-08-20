# `monad_fiber` design notes

## Goals and overview

A fiber library generally consists of three parts:

1. The fibers themselves
2. The synchronization primitives needed for fibers to communicate
   with each other; without these, fibers could only yield or
   return
3. Some kind of scheduler, which makes a sleeping fiber runnable
   again when a synchronization primitive signals that a resource
   is ready, so the fiber(s) waiting for it can wake up

This code makes an effort to be much simpler than a typical fiber library,
which is often a full-fledged "framework." In this lightweight library,
the coupling between the three parts is minimal, and occurs in only a few
lines of code. Thus the design can be changed quickly to whatever our
internal needs are, rather than being a general purpose library.

The implementation is also meant to be clear;  ideally a programmer can
understand it fully without much trouble. Take this with a grain of salt
though: context-switching code can be tricky, so understanding all the
implementation details will require some time investment!

### "Hello, world!" using fibers

The following listing shows a "Hello, World!" example written in C that
only uses  the fibers themselves -- there are no synchronization primitives
and thus there is no scheduling. The fiber print a "Hello, World!" style
message three times, suspending itself after each time. After the last
message, it finishes.

```.c
#include <assert.h>
#include <err.h>
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sysexits.h>

#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_util.h>

// This is the function that will run on the fiber
uintptr_t say_hello_fiber_function(uintptr_t arg)
{
  // The fiber greets you by your name, which is passed in as the fiber
  // function's argument
  const char *const name = (const char*)arg;

  // Say hello, then suspend the fiber
  printf("Hello, %s!\n", name);
  monad_fiber_yield(0);

  // When we reach here, we've been run again; we resume from the
  // suspension point of the yield immediately above. We'll say hello
  // again, then suspend again
  printf("Welcome back, %s!\n", name);
  monad_fiber_yield(0);

  // Resumed for the final time; say goodbye, then return. Returning from
  // the fiber function suspends the fiber until it is given a new function
  // to run
  print("Farewell, %s!\n", name);
  return 0;
}

int main(int argc, char **argv) {
  int rc;
  monad_fiber_t hello_fiber;
  monad_fiber_stack_t fiber_stack;
  const char *name;
  const size_t fiber_stack_size = 1UL << 17; // A 128 KiB stack
  
  // This application says hello to you using a fiber; it expects your name
  // as the first (and only) positional argument
  if (argc != 2)
    errx(EX_USAGE, "usage: %s <your-name>", argv[0]);
  name = argv[1];

  // We start by allocating a stack for the fiber. You can do this manually,
  // but in this example we'll use a helper function (from fiber_util.h)
  // to call mmap(2) and set up some stack overflow guard pages
  rc = monad_fiber_alloc_stack(&fiber_stack_size, &fiber_stack);
  if (rc != 0)
    errc(1, rc, "monad_fiber_alloc_stack failed: %s", strerror(rc));

  // Initialize the fiber, passing in our stack
  monad_fiber_init(&hello_fiber, fiber_stack);

  // Tell the fiber what function to run; the second argument is
  // the scheduling priority, which doesn't matter in this example;
  // the last parameter is passed into the fiber function, as the
  // argument. We pass a pointer to our name
  monad_fiber_set_function(&hello_fiber, MONAD_FIBER_PRIO_HIGHEST,
                           say_hello_fiber_function, (uintptr_t)name);

  // Run the fiber until the first suspension point; this will print
  // "Hello, <name>!", suspend the fiber function, and then our call to
  // monad_fiber_run will return. If nothing goes wrong, the return code
  // will be 0. The second parameter (which is nullptr here) allows us to
  // obtain information about why the fiber suspended; in this example we
  // don't care, so we pass nullptr
  rc = monad_fiber_run(&hello_fiber, nullptr);
  ASSERT(rc == 0);
  
  // Run the fiber again, until it yields again; this will print
  // "Welcome back, <name>!" and then yield back to us once more
  rc = monad_fiber_run(&hello_fiber, nullptr);
  ASSERT(rc == 0);
  
  // Run the fiber a final time. This will print "Farewell, <name>!" and then
  // the fiber function will return. The return won't look much different to us
  // than the yields above: the fiber will suspend and monad_fiber_run will
  // return 0 to us, as before. The difference is, we can't run the fiber again.
  // If, instead of passing nullptr as the second argument, we instead passed
  // a pointer to a `monad_fiber_suspend_info_t`, we could get more information
  // about the suspension. Namely, that it was a return and not a yield, and we
  // could also read the return code. However, we don't care in this example.
  rc = monad_fiber_run(&hello_fiber, nullptr);
  ASSERT(rc == 0); 

  // Try to run the fiber one more time; we can't do it since the fiber
  // function returned, so this will fail and return the errno-domain error
  // code ENXIO
  rc = monad_fiber_run(&hello_fiber, nullptr);
  ASSERT(rc == ENXIO);

  // At this point, we could reuse the fiber's resources to run the function
  // a second time. To prepare for a second run, we would reset the function: 
  monad_fiber_set_function(&hello_fiber, MONAD_FIBER_PRIO_HIGHEST,
                           say_hello_fiber_function, (uintptr_t)name);

  // However, that's enough for today. Nothing special needs to be done to
  // destroy the fiber itself, as there is no dynamic memory allocation.
  // The fiber stack though, was allocated via mmap(2) and needs to be
  // freed.
  monad_fiber_free_stack(fiber_stack);
  
  return 0;
}
```

## Where is the code?

1. For the fibers themselves:
   - `fiber.h` - defines the interface for fibers, i.e., the public
     functions and the central `monad_fiber_t` structure
   - `fiber.c` - most of the fiber implementation
   - `fiber_thr.c` - an implementation file, related to the "thread fiber"
      feature (see the **Thread fibers** section later on)
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
   - `future.hpp` - defines the C++ types `simple_future<T>` and
     `simple_promise<T>`; these are similar to (but less fully-featured than)
     those found in C++11 `<future>`; `simple_promise<T>` is implemented
     using `monad_fiber_channel_t`, whereas the `simple_promise<void>`
     specialization uses `monad_sempaphore_t`

3. The "scheduler"
   - `monad_run_queue.h` - defines the interface for a simple thread-safe
     priority queue of `monad_fiber_t*` objects; 
   - `monad_run_queue.c` - implementation file for `monad_run_queue.h`

### Why is "scheduler" in quotes above?

To keep the design simple and less monolithic, the `monad_fiber` library does
not have a full-fledged scheduler, or any higher-level abstractions such as a
task pool, run-loop, worker threads, etc.

The intention is for the user code to solve its problem directly, creating
complex objects only if it needs them, and using `monad_fiber` as a bare-bones
helper module. The only point of coupling between the three parts of a fiber
system is the priority queue, `monad_run_queue_t`.

A `monad_fiber_t` keeps track of an associated `monad_run_queue_t*`, and when
the fiber is signaled for wakeup by a synchronization primitive, the fiber
"wakes up" by re-enqueueing itself back on this associated priority queue.

The library does not run anything by itself. Instead it offers a single
function (`monad_fiber_run`) to start or resume a fiber, which runs the fiber's
function until that function reaches a suspension point -- at which point
`monad_fiber_run` just returns. The library does little beyond that.

The only other "automatic" thing it does is re-enqueue the fiber on a priority
queue if a synchronization primitive wakes the fiber. The user of the library
must create their own concepts like worker threads, pools, etc. to
enqueue/dequeue fibers from a `monad_run_queue_t`. The exact topology and way
of doing this is not specified by the library.

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
When the fiber suspends, the current thread will beginning executing the
code for a different fiber. The suspended fiber may later be resumed, at
which point execution continues at the point where it left off.

Most of the implementation can be understood by thinking about exactly
how and when a fiber switches. The model we follow is:

- A fiber is started or resumed by calling the `monad_fiber_run`
  function, passing in the `monad_fiber_t*` that the user wants to run;
  that is, the context that _calls_ `monad_fiber_run` will switch into the
  given fiber and begin (or resume) running its associated function

- In general, when a fiber suspends for any reason (yield, sleeping,
  returning, etc.), it jumps back to the context that was executing
  previously. This is the context that was running the code for
  `monad_fiber_run` in the first place, so the suspension of a fiber
  appears to the caller of `monad_fiber_run` as the `monad_fiber_run`
  function returning back to them

- In general then, the function that calls `monad_fiber_run` is
  a lightweight scheduler: it decides to run fibers somehow, and
  calls `monad_fiber_run` in a loop, with the sequence of fibers it
  wishes to run

- The most obvious design is to use a single global priority queue
  (a `monad_run_queue_t` object). Each worker takes the
  next-highest-priority fiber and runs it until it suspends

Here is an example of how you might build such a worker thread (this
is just an API example, the current implementation is more complex):

```c
int rc;
monad_fiber_t *fiber;
monad_fiber_suspend_info_t suspend_info;
monad_run_queue_t *const run_queue = /* initialize a fiber priority queue*/

while (!atomic_load(&done)) {
  // Poll the priority queue for the highest priority fiber that's ready
  // to run
  fiber = monad_run_queue_try_pop(run_queue);

  if (fiber == nullptr)
    continue; // Nothing is ready to run, poll again

  // Run the fiber until it suspends
  rc = monad_fiber_run(fiber, &suspend_info);

  if (rc != 0) {
      /* something went wrong */
  }
  if (suspend_info.suspend_type == MONAD_FIBER_SUSPEND_RETURN) {
      /* fiber function returned; can't run it anymore */
  }
}
```