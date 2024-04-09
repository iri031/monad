# Proposed replacement executor

## Features:

1. 100% C throughout, easing FFI into Rust and other languages.
2. 100% priority based, with three levels of individual priority for
CPU and I/O.
3. 100% deterministic in the hot path so long as new work is launched
from the same thread as the executor: no thread synchronisation, no malloc,
no unbounded loops. 100% wait free, unless waits are requested.
4. Tasks can be launched on executors running on non-local kernel threads,
thus making implementing a priority-based kernel thread pool very
straightforward.
5. Tasks have their own stacks and can be arbitrarily suspended and
resumed.
6. Integrated ultra-lightweight CPU timestamp counter based time tracking
throughout.

## Benchmarks:

### Cold code:

#### Launch new work on executor:
- Time between launching a new task and it beginning execution: **490 ns**.
- Time between a task beginning execution and it being wound up: **240 ns**.
   
#### Launch new work on executor which suspends on an i/o, resumes and then exits
- Time between launching a new task and it beginning execution: **490 ns**.
- Time between a task beginning execution and it initiating the
i/o with io_uring, and then suspending awaiting the i/o completion: **660 ns**.
- Time between i/o completing and task resumption: **10 ns**.
- Time between task resumption and it being would up: **240 ns**.

### Hot code showing superscalar execution capability:
- Hot loop initiating, executing and tearing down tasks: **73.0563 ns**/op.

- Hot loop suspend-resuming a task using an io_uring noop (i.e. minimum
possible io_uring op overhead): **83.329 ns**/op.

## Example of use:

```c
monad_async_result r;

monad_async_executor ex;
struct monad_async_executor_attr ex_attr;
memset(&ex_attr, 0, sizeof(ex_attr));
ex_attr.io_uring_ring.entries = 64;
r = monad_async_executor_create(&ex, &ex_attr);  // expensive
CHECK_RESULT(r);

monad_async_task task;
struct monad_async_task_attr t_attr;
memset(&t_attr, 0, sizeof(t_attr));
r = monad_async_task_create(&task, &t_attr);  // expensive
CHECK_RESULT(r);
task->priority.cpu = monad_async_priority_high;
task->user_code = myfunc;
task->user_ptr = myptr;

// From now on cheap and deterministic in the hot path
// Schedule this task for execution
r = monad_async_task_attach(ex, task);
CHECK_RESULT(r);
...
// Executor run loop
r = monad_async_executor_run(ex,
  1,       // max items to complete this run
  nullptr  // optional struct timespec timeout, can be {0, 0}
);
CHECK_RESULT(r);
// r.value is the number of items of work done
...
// Back to expensive operations
r = monad_async_task_destroy(task);
CHECK_RESULT(r);
r = monad_async_executor_destroy(ex);
CHECK_RESULT(r);
```

A task looks like this:

```c
static monad_async_result myfunc(monad_async_task task)
{
  /* do stuff */

  // Suspend and resume after one second
  r = monad_async_task_suspend_for_duration(task, 1000000000ULL);
  CHECK_RESULT(r);

  // All done, return success
  return monad_async_make_success(0);
}
```

## Todo

- Yet to replace setjmp/longjmp based context switching with something
much better (Klemens' code).
- A test should make 1 billion tasks to prove it works without issue.
- Timeout is not scaling nanoseconds to BOOTTIME clock yet.
- Task total ticks executing appears to be too low?
- Executor run max items not being observed for task launches yet.
- SQE submission queue overflow not handled yet.
