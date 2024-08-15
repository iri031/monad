# Proposed replacement executors and core runloops

## Features (i/o executor `monad_async`):

1. 100% C throughout, easing FFI into Rust and other languages.
2. 100% priority based, with three levels of individual priority for
CPU and I/O.
3. 100% deterministic in the hot path so long as new work is launched
from the same thread as the executor: no thread synchronisation, no malloc,
no unbounded loops. 100% wait free, unless waits are requested or work
is posted from foreign kernel threads.
4. Tasks can be launched on executors running on non-local kernel threads,
thus making implementing a priority-based kernel thread pool very
straightforward.
5. Tasks have runtime pluggable context switching implementations, which
allows zero overhead support for C++ or Rust coroutines.
6. Integrated ultra-lightweight CPU timestamp counter based time tracking
throughout.
7. Async file i/o: open, close, read, write, sync range, durable sync.
8. Async socket i/o: open, close, read, write, bind, listen, transfer
to i/o uring, connect, shutdown.
9. Auto loaded GDB pretty printers for context switchers (showing all
child contexts), and contexts themselves (showing runstate and current
stack frame).

## Examples of use:

### Execute a task on an i/o executor
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
  r = monad_async_task_suspend_for_duration(nullptr, task, 1000000000ULL);
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

Work dispatcher is simple but fast -- any executor which finds itself with
no work to do dequeues a new piece of work from the work dispatcher queue.

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
  monad_async_result r;

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

### File i/o

From a task's perspective, file i/o is implemented in the same way as how the
NT kernel's alertable i/o is implemented, which to my best knowledge is the
optimal way. There is a queue of initiated i/o and another queue of completed
i/o. When your task suspends, i/o can move from the initiated queue to the
completed queue. When your task resumes, it is on you to dequeue any completed
i/o.

As with the NT kernel's `IOSTATUS` structure which uniquely identifies each
i/o in flight, the `monad_async_io_status` structure does the same. You supply
the `monad_async_io_status` structure instance for every i/o you initiate. It
will get asynchronously completed with the result of the i/o.

Registered buffer i/o is supported. For writes, you claim a registered buffer,
write into it and initiate the write. For reads, io_uring allocates the
registered buffer, and tells you the buffer on read completion.

```c
static monad_async_result mytask(monad_async_task task)
{
  monad_async_result r;

  // Open a file for read. This will suspend the task and resume
  // it after the file has been opened.
  struct open_how how = {
      .flags = O_RDONLY, .mode = 0, .resolve = 0
  };
  monad_async_file fh;
  r = monad_async_task_file_create(&fh, task, nullptr, "foo.txt", &how);
  CHECK_RESULT(r);

  // Initiate a read. It may suspend and resume the task if there
  // are no more io_uring sqes available.
  monad_async_io_status iostatus;
  monad_async_executor_registered_io_buffer buffer;
  memset(&iostatus, 0, sizeof(iostatus));
  monad_async_task_file_read(
      &iostatus,     // i/o status to use
      task,          // this task
      fh.get(),      // open file to use
      &buffer,       // registered buffer chosen
      128,           // max bytes to read
      0,             // offset to use
      0);            // preadv2 flags to use

  // Reap i/o completions, suspending the task until more completions
  // appear
  for(;;){
    monad_async_io_status *completed;
    r = monad_async_task_suspend_until_completed_io(&completed, task, (uint64_t)-1);
    CHECK_RESULT(r);
    if(r.value == 0) {
      break;
    }
    /* handle completed ... */
  }

  // Release the registered buffer
  r = monad_async_executor_release_registered_io_buffer(
                          task->current_executor, buffer.index);
  CHECK_RESULT(r);

  // Close the file, This will suspend the task and resume it
  // after the file has been closed.
  r = monad_async_task_file_destroy(task, fh);
  CHECK_RESULT(r);

  // All done, return success
  return monad_async_make_success(0);
}

```

## Todo

- Actually implement ring provided buffers.
- Executor `total_io_completed` never seems to match `total_io_submitted`,
with them sometimes being very very different. I have walked the code many
times and I don't see the cause :(
- A context switcher based on Klemens' Boost.Context port
- When a task exits, all i/o still occurring on that task ought to be pumped and dumped out.
- Need to test cancellation works at every possible lifecycle and suspend state
a task can have.
- A context switcher implementing C++ coroutines would be nice. Some notes
on that:
    - MSVC coroutine frame: Promise | Frame prefix | Local variables. Coroutine
frame is: `struct msvc_frame_prefix { void(*factivate)(void*); uint16_t index, flag; };`.
Implementation is a state machine based on switching `index`.
    - GCC/clang coroutine frame: Frame prefix | Promise | Unknown | Local
variables. Coroutine frame is: `struct clang_frame_prefix { void(*factivate)(void*); void(*fdestroy)(void*);};`.
- GDB showing current suspended backtraces of contexts would be nice.

Here is qemu's GDB helper for their coroutines: https://gitlab.com/qemu-project/qemu/-/blob/master/scripts/qemugdb/coroutine.py

An example GDB python helper to teach GDB about fiber stack frames:

```
# For the https://github.com/geofft/vireo green thread library
import gdb

thread_map = {}

main_thread = None

# From glibc/sysdeps/unix/sysv/linux/x86/sys/ucontext.h
x8664_regs = [ 'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14',
               'r15', 'rdi', 'rsi', 'rbp', 'rbx', 'rdx', 'rax',
               'rcx', 'rsp', 'rip', 'efl', 'csgsfs', 'err',
               'trapno', 'oldmask', 'cr2' ]

def vireo_current():
    return int(gdb.parse_and_eval('curenv')) + 1

class VireoGreenThread:
    def __init__(self, tid):
        self.tid = tid

    def _get_state(self):
        return gdb.parse_and_eval('envs')[self.tid]['state']

    def fetch(self, reg):
        """Fetch REG from memory."""
        global x8664_regs
        global thread_map
        thread = thread[self.tid]
        state = self._get_state()
        gregs = state['uc_mcontext']['gregs']
        for i in range(0, len(x8664_regs)):
            if reg is None or reg == x8664_regs[i]:
                thread.write_register(x8664_regs[i], gregs[i])

    def store(self, reg):
        global x8664_regs
        global thread_map
        thread = thread[self.tid]
        state = self._get_state()
        gregs = state['uc_mcontext']['gregs']
        for i in range(0, len(x8664_regs)):
            if reg is None or reg == x8664_regs[i]:
                gregs[i] = thread.read_register(x8664_regs[i])

    def name(self):
        return "Vireo Thread " + str(self.tid)

    def underlying_thread(self):
        if vireo_current() == self.tid:
            global main_thread
            return main_thread
        return None

class VFinish(gdb.FinishBreakpoint):
    def stop(self):
        tid = int(self.return_value) + 1
        global thread_map
        thread_map[tid] = gdb.create_green_thread(tid, VireoGreenThread(tid))
        return False

class VCreate(gdb.Breakpoint):
    def stop(self):
        VFinish(gdb.newest_frame(), True)
        return False

class VExit(gdb.Breakpoint):
    def stop(self):
        global main_thread
        if main_thread is None:
            main_thread = gdb.selected_thread()
        global thread_map
        tid = vireo_current()
        if tid in thread_map:
            thread_map[tid].set_exited()
            del thread_map[tid]

VCreate('vireo_create', internal=True)
VExit('vireo_exit', internal=True)
```
