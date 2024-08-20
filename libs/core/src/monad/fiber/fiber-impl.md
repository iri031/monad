# `monad_fiber` implementation notes

## Basic design
The fiber implementation has two layers:

1. **Machine-independent layer** - this is shared by all architectures
   and addresses how the fibers transfer control between each other; most
   of this code is in `fiber.c`, with some details in `fiber_thr.c`

2. **Machine-dependent layer** - this consists of only two functions,
   `monad_make_fcontext` and `monad_jump_fcontext` which were imported
   from the Boost.Context third-party library. These are the original
   names of the functions, but with the `monad_` prefix added. They are
   the low-level context switch functions implemented in assembly
   language for a particular CPU architecture, calling convention, and ABI.

### Machine-independent switching

The machine-independent part of the fiber switch is handled in two phases
(called "start switch" and "finish switch"), which happen by calling
two functions in `fiber.c`:

```.h
struct monad_transfer_t
monad_fiber_start_switch(monad_fiber_t *cur_fiber, monad_fiber_t *next_fiber,
                         enum monad_fiber_state cur_suspend_state,
                         enum monad_fiber_suspend_type cur_suspend_type,
                         uintptr_t eval);

extern monad_fiber_suspend_info_t
_monad_fiber_finish_switch(struct monad_transfer_t xfer_from);
```

`_monad_fiber_finish_switch` starts with an underscore to emphasize that it
is intended to be an internal function, even though it has external linkage
so that `fiber_thr.c` can call it. `monad_fiber_start_switch` has internal
linkage, and is only called inside `fiber.c`.

The suspension points (`monad_fiber_yield`, `_monad_fiber_sleep`, and the
fiber function return stub), instead call this slightly-higher-level wrapper,
which will switch to the previously-executing fiber, and return when our
fiber is resumed:

```.h
extern void _monad_fiber_suspend(monad_fiber_t *cur_fiber,
                                 enum monad_fiber_state cur_suspend_state,
                                 enum monad_fiber_suspend_type cur_suspend_type,
                                 uintptr_t eval);
```

Some details of how "start_switch" and "finish_switch" work:

- To perform a switch, we have a notion of the current fiber (which
  will be *switched from* and thus suspended) and a next fiber
  (which will be *switched to*, and thus resumed)

- There are two functions because during "start switch", we're still running
  on the "switched from" stack, and during "finish switch" we're running
  on the "switched to" stack

- When `monad_fiber_start_switch` is called, we are running on the stack
  of the current fiber; this function performs some book-keeping and calls
  the machine-dependent switch function, which causes the switch to happen
  at the CPU level

- Immediately after the CPU-level switch happens, we are running on the
  stack of the resumed (or newly-started) fiber, and the previously running
  fiber is now suspended; this resumption site must immediately call
  `_monad_fiber_finish_switch` to complete the switch; we also have access
  to the `struct in_progress_fiber_switch` of the suspended fiber we just
  switched from and the machine-dependent context pointer of its suspension
  point via the `struct monad_transfer_t` object

- The resumption can only happen at well-defined locations: namely the start
  of the fiber, or immediately after the suspension "returns" (see the next
  point). This is the place where we must call `_monad_fiber_finish_switch`

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

- Keep in mind that although we typically jump back to the previously
  executing fiber, that does not mean that two fibers are forever linked
  together in a pair. Typically a task fiber will *migrate* between
  threads, as each worker thread selects the highest priority fiber that
  is ready to run

To understand this last point (which is the cause of most bugs), please
read the section on "thread fibers", and then consider this example with
three fibers:

1. `monad_fiber_t *the_task` - fiber running a task we care about
2. `monad_fiber_t *thr_1` - thread fiber of "fiber pool" worker thread
3. `monad_fiber_t *thr_2` - thread fiber of a different fiber pool worker
   thread

When our task originally starts running, it is because `monad_fiber_run`
was called from `thr_1`. When the `the_task` suspends, control is returned
to `thr_1`. Suppose the suspension occurs because of some complex
synchronization condition that will be unblocked far in the future.

When `the_task` is ready to be woken up, it is re-added to a
`monad_run_queue_t`. Suppose that `thr_1` is busy when this happens, so it
ends up being the `thr_2` worker that pops the `the_task` from the priority
queue.

In this case `the_task` will be restarted at the suspension point,
but when returning from `_monad_fiber_suspend`, the `prev_fiber` will not be
the same as it originally was (originally, it was `thr_1`, now it is
`thr_2`).

An in-progress switch is described by the internal structure
`struct in_progress_fiber_switch`, which is passed between the start
and finish halves of the fiber context switch. When we *start* a fiber
switch, the `struct in_progress_fiber_switch` represents the switch we
are initiating -- our fiber is the `monad_fiber_t *switch_from` member.
When `monad_jump_fcontext` *returns*, the return value contains the
`struct in_progress_fiber_switch *` describing our resumption, initiated
from somewhere else (possibly a different worker thread). Now our fiber
is the `monad_fiber_t *switch_to` member.

## Thread fibers / what is `fiber_thr.c`?

Most fibers are user-created, but in the current db implementation, an
ordinary thread of execution is sometimes treated as though it is running on
a fiber. This is an API idiom that Boost.Fiber allowed, thus the
existing db code grew to rely on it.

For this to work, we need to make an ordinary thread context pretend that it
is a fiber. This is called a "thread fiber" in the code. To simplify
`fiber.c`, most of the code for thread fiber support lives in a different
file, `fiber_thr.c`.  This is because thread fibers are special in several
ways, thus they are easy to separate out and not complicate the core
implementation file.

There are two parts of thread fiber support:

1. Creating a "fake" `monad_fiber_t` that represents a thread context; this
   is what is returned if you call `monad_fiber_self()` in the context of a
   normal thread rather than in a "real" fiber

2. Creating a dummy "wakeup fiber" that the thread fiber switches to, when
   it goes to sleep on a wait channel. For performance reasons, the wakeup
   fiber spins until it is woken up

### Thread fibers improve code quality

Although thread fibers were created to avoid rewriting legacy database
code, they clean up the implementation significantly. Even if there were
no legacy database code that needed thread fibers, it might still make
good engineering sense to add them, given that they make the implementation
easier to understand.

By modeling the regular thread execution context as a "fake" fiber, we
create a nice symmetry in code: both the previous execution context and
the next execution context are explicitly modeled as fibers, i.e., there
is a `monad_fiber_t` object describing both of them. This makes the core
implementation (in `fiber.c`) indifferent to whether an execution context
is a "native thread" context or a "real fiber" context. The details that
make the illusion work are moved out of the way, into `fiber_thr.c`.
This allows the low-level switching machinery, e.g. `struct
in_progress_fiber_switch` and the functions that use it, to represent both
halves of the switch as just two `monad_fiber_t*` instances, even though
they are usually different kinds of contexts.

In practice, it is always thread fibers that run lightweight scheduling
algorithms and call `monad_fiber_run`. You could build more complex chains
of fibers that call each other, but currently we do not.