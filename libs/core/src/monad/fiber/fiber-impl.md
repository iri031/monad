# `monad_fiber` implementation notes

## Basic design

The fiber implementation has three essential objects:

1. `monad_thread_executor_t` - much the same way as a single CPU
   is an execution resource to run threads, a single thread is an
   execution resource to run fibers. Each thread (and its execution
   state needed to run fibers) that wants to call `monad_fiber_run`
   is explicitly represented by a `monad_thread_executor_t` object; the
   first time a thread calls `monad_fiber_run`, one of these objects is
   created to represent it

2. `struct monad_exec_context` - this object represents an execution context
   (i.e., what is actually running on a thread) which can be suspended to
   context switch into something else, on that same thread. There are
   two kinds of contexts: the context of an ordinary system thread, and the
   context for a fiber

3. `monad_fiber_t` - this is essentially a `struct monad_exec_context`,
   augmented with the additional fields needed to be a proper user fiber,
   e.g., a scheduling priority, the fiber function that the user wishes
   to run, etc.

## Context switching

Most of the context switching code switches between two
`struct monad_exec_context` objects, *not* between two fibers. This is
because, in a typical context switch, one of the execution contexts is
for a fiber context, and the other one is an ordinary thread context
(i.e., the context that called `monad_fiber_run`). The context switching
itself is divided into two layers:

1. **Machine-independent layer** - this is shared by
   all architectures and addresses how the execution contexts transfer
   control between each other; this code is in `fiber.c`

2. **Machine-dependent layer** - this consists of only two functions,
   `monad_make_fcontext` and `monad_jump_fcontext` which were imported
   from the Boost.Context third-party library. These are the original
   names of the functions, but with the `monad_` prefix added. They are
   the low-level context switch functions implemented in assembly
   language for a particular CPU architecture, calling convention, and ABI.
   The `md` in the structure field `md_suspended_ctx` stands for
   "machine-dependent".

### Machine-independent switching

The machine-independent part of the fiber switch is handled in two phases
(called "start switch" and "finish switch"), which happen by calling
two functions in `fiber.c`:

```.h
static struct monad_transfer_t
start_context_switch(
    struct monad_exec_context *cur_exec,
    struct monad_exec_context *next_exec,
    enum monad_exec_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval);

static monad_fiber_suspend_info_t
finish_context_switch(struct monad_transfer_t xfer_from);
```

The suspension points (`monad_fiber_yield`, `_monad_fiber_sleep`, and the
fiber function return stub), instead call this slightly-higher-level wrapper,
which will switch to the previously-executing context, and will return when
resumed from the suspension point:

```.h
static void suspend_fiber(
    struct monad_exec_context *cur_exec,
    enum monad_exec_state cur_suspend_state,
    enum monad_fiber_suspend_type cur_suspend_type, uintptr_t eval)
```

Some details of how "start_context_switch" and "finish_context_switch" work:

- To perform a switch, we have a notion of the current execution context
  (which will be *switched from* and thus suspended) and a next execution
  context (which will be *switched to*, and thus resumed)

- There are two functions because during "start switch", we're still running
  on the "switched from" stack, and during "finish switch" we're running
  on the "switched to" stack

- When `start_context_switch` is called, we are running on the "switched
  from" stack; this function performs some book-keeping and calls the
  machine-dependent context switch function, which causes the stack
  switch to happen at the CPU level

- Immediately after the CPU-level switch happens, we are running on the
  stack of the resumed (or newly-started) execution context, and the
  previously running context is now suspended; this resumption site must
  immediately call `finish_context_switch` to complete the switch; we also
  have access to the `monad_thread_executor_t` of the thread we are now
  running on, and the machine-dependent context pointer of its suspension
  point via the `struct monad_transfer_t` object

- The resumption can only happen at well-defined locations: namely the start
  of a fiber, or immediately after the suspension "returns" (see the next
  point). This is the place where we must call `finish_context_switch`

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
  executing context, that does not mean that context fibers are forever
  linked together in a pair. Typically a fiber will *migrate* between
  threads, as each worker thread selects the highest priority fiber that
  is ready to run; this is why the `monad_thread_executor_t` is passed
  between the low-level jump routines: when a fiber is resumed on a
  different thread than it was originally suspended on, this value
  will be different upon resumption than it was at suspension

To understand this last point (which is the cause of most bugs), consider
this example with three execution contexts:

1. `monad_fiber_t *the_task` - a fiber running a task we care about; this
   object contains an execution context inside it, as `the_task->exec_ctx`
2. `monad_thread_executor_t *thr_1` - for exposition purposes, we give this
   explicit name to the `thread_local` object which is used when thread 1
   runs our fiber; this also has an execution context inside of it, as 
   `thr_1->thread_ctx`
3. `struct monad_exec_context *thr_2` - as above, for thread 2

When our task originally starts running, it is because `monad_fiber_run`
was called from `thr_1`. When the `the_task` suspends, control is returned
to `thr_1`. Suppose the suspension occurs because of some complex
synchronization condition that will be unblocked far in the future.

When `the_task` is ready to be woken up, it is re-added to a
`monad_run_queue_t`. Suppose that `thr_1` is busy when this happens, so it
ends up being the `thr_2` worker that pops the `the_task` from the priority
queue.

In this case `the_task` will be restarted at the suspension point,
but when returning from `suspend_fiber`, the `prev_exec` context will not
be the same as it originally was (originally, it was `thr_1->thread_ctx`,
now it is `thr_2->thread_ctx`).

The `monad_thread_executor_t*` representing the host thread is passed between
the start and finish halves of the context switch. When we *start* a context
switch, the `monad_thread_executor_t` represents the thread we are running on.
When `monad_jump_fcontext` *returns*, it gives us a new value for the
`monad_thread_executor_t*`. This is for the host thread which resumed us,
which may be different.