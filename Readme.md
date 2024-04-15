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

### Single execution:

#### Launch new work on executor:
- Time between launching a new task and it beginning execution: **100 ns**.
- Time between a task beginning execution and it being wound up: **90 ns**.
   
#### Launch new work on executor which suspends on an i/o, resumes and then exits
- Time between launching a new task and it beginning execution: **130 ns**.
- Time between a task beginning execution and it initiating the
i/o with io_uring, and then suspending awaiting the i/o completion: **120 ns**.
- Time between i/o completing and task resumption: **50 ns**.
- Time between task resumption and it being wound up: **120 ns**.

### Superscalar execution:
- Loop initiating, executing and tearing down tasks: **39.6 ns**/op (4.8x, CPU is
capable of 5x).

- Loop suspend-resuming a task using an io_uring noop (i.e. minimum
possible io_uring op overhead): **85.766 ns**/op (3.38x, io_uring cycle is
not superscalar friendly).

## Example of use:

### Execute a task on an executor
```c
monad_async_result r;

// Create an executor
monad_async_executor ex;
struct monad_async_executor_attr ex_attr;
memset(&ex_attr, 0, sizeof(ex_attr));
ex_attr.io_uring_ring.entries = 64;
r = monad_async_executor_create(&ex, &ex_attr);  // expensive
CHECK_RESULT(r);

// Create a context switcher
// Each task can have its own context switcher, and the executor
// will suspend and resume that task with its context switcher
// You can have as many context switcher types per executor as
// you like. This is a setjmp/longjmp context switcher. There
// can be many others.
monad_async_context_switcher switcher_sjlj;
r = monad_async_context_switcher_sjlj_create(&switcher_sjlj);
CHECK_RESULT(r);

// Create a task. Creating these is expensive, but they can be
// reused very efficiently when they complete their assigned work.
monad_async_task task;
struct monad_async_task_attr t_attr;
memset(&t_attr, 0, sizeof(t_attr));
r = monad_async_task_create(&task, switcher_sjlj, &t_attr);  // expensive
CHECK_RESULT(r);

// Set what work this task will do and its priority
task->priority.cpu = monad_async_priority_high;
task->user_code = myfunc;
task->user_ptr = myptr;

// From now on cheap and deterministic in the hot path

// Schedule this task for execution. This is threadsafe, which
// lets you easily build thread pools of high performance executors
r = monad_async_task_attach(ex, task, nullptr);
CHECK_RESULT(r);

...

// Executor run loop
r = monad_async_executor_run(ex,
  1,       // max items to complete this run
  nullptr  // optional struct timespec timeout, can be {0, 0}
);
CHECK_RESULT(r);
// r.value is the number of items of work done, ETIME if it timed
// out and no work was done.

...

// Back to expensive operations. In C++ these can be easily wrapped
// into unique_ptrs (c.f. cpp_helpers.hpp)
r = monad_async_task_destroy(task);
CHECK_RESULT(r);
r = monad_async_context_switcher_destroy(switcher_sjlj);
CHECK_RESULT(r);
r = monad_async_executor_destroy(ex);
CHECK_RESULT(r);
```

### Task

The task object can be reused for different work after the work
completes.

```c
static monad_async_result myfunc(monad_async_task task)
{
  /* do stuff */

  // Suspend and resume after one second
  r = monad_async_task_suspend_for_duration(task, 1000000000ULL);
  CHECK_RESULT(r);

  // You could also read from a socket, write to a file, do any
  // other operation which io_uring supports. They all appear as
  // suspend and resume. If the context switcher for this task
  // were a C++ coroutine switcher, this function could be a C++
  // coroutine and it would work seamlessly and with no loss of
  // efficiency.

  // All done, return success
  return monad_async_make_success(0);
}
```

### Work dispatching to a thread pool

Currently being implemented, but will look like this:

```c
monad_async_result r;
monad_async_task tasks[1024];  // tasks

// Create a work dispatcher
monad_async_work_dispatcher wd;
struct monad_async_work_dispatcher_attr wd_attr;
memset(&wd_attr, 0, sizeof(wd_attr));
r = monad_async_work_dispatcher_create(&wd, &wd_attr);  // expensive
CHECK_RESULT(r);

// Create executors on thread to execute work
// (see below)
create_executors_on_threads(wd);

// Submit tasks to be executed. Each task's CPU priority will
// determine which get executed first.
r = monad_async_work_dispatcher_submit(wd, tasks, 1024);
CHECK_RESULT(r);

// Wait until all tasks have been dispatched and executed
r = monad_async_work_dispatcher_wait(wd, 0, 0, nullptr);
CHECK_RESULT(r);

// Tell all executors to quit
r = monad_async_work_dispatcher_quit(wd, MAX_SIZE_T, nullptr);
CHECK_RESULT(r);

// Cleanup
r = monad_async_work_dispatcher_destroy(wd);
CHECK_RESULT(r);
```

An executor thread would look like:

```c
void worker_thread(monad_async_work_dispatcher wd)
{
  struct monad_async_work_dispatcher_executor_attr ex_attr;
  memset(&ex_attr, 0, sizeof(ex_attr));
  // Don't create an io_uring for this executor
  // This makes it into a pure-compute executor incapable of doing i/o
  ex_attr.executor.io_uring_ring.entries = 0;
  r = monad_async_work_dispatcher_executor_create(&ex, wd, &ex_attr);
  CHECK_RESULT(r);

  // Loop executing work until told to quit
  for(;;)
  {
    r = monad_async_work_dispatcher_executor_run(ex);
    CHECK_RESULT(r);
    if(r.value < 0)
    {
      break;
    }
  }

  // Cleanup
  r = monad_async_work_dispatcher_executor_destroy(ex);
  CHECK_RESULT(r);
}
```

## Todo

- Need to test cancellation works
- Yet to replace setjmp/longjmp based context switching with something
much better (Klemens).
- A test should make 1 billion tasks to prove it works without issue
and scales without issue.
- SQE submission queue overflow not handled yet.
    - Needs yet to be written "resumption queue" facility which lets
you suspend tasks into a specific queue which can then be resumed
based on some condition e.g. there are now SQE entries free.
- Rust's bindgen does not generate Rust atomics from C atomics, which
is rather irritating. https://github.com/rust-lang/rust-bindgen/issues/2151
is the issue tracker for it, looks like somebody just needs to go implement
support and submit a PR.
