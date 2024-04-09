#include "task_impl.h" // MUST BE FIRST INCLUDE

// #define MONAD_ASYNC_EXECUTOR_PRINTING 1

#include "monad/async/executor.h"

#include "monad/async/task.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <threads.h>

#include <linux/ioprio.h>

struct monad_async_executor_impl
{
  struct monad_async_executor_head head;

  thrd_t owning_thread;
  bool within_run;
  struct context run_context;
  struct io_uring ring, wr_ring;
  LIST_DEFINE_P(tasks_running, struct monad_async_task_impl);
  LIST_DEFINE_P(tasks_suspended_awaiting, struct monad_async_task_impl);
  LIST_DEFINE_P(tasks_suspended_completed, struct monad_async_task_impl);

  // all items below this require taking the lock
  atomic_int lock;
  int tasks_pending_launch_next_queue;
  // Note NOT sorted by task priority!
  LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
};

monad_async_result monad_async_executor_create(monad_async_executor *ex, struct monad_async_executor_attr *attr)
{
  if (attr->io_uring_ring.entries == 0)
  {
    return monad_async_make_failure(EINVAL);
  }
  struct monad_async_executor_impl *p = (struct monad_async_executor_impl *)calloc(1, sizeof(struct monad_async_executor_impl));
  if (p == nullptr)
  {
    return monad_async_make_failure(errno);
  }
  p->owning_thread = thrd_current();
  int r = io_uring_queue_init_params(attr->io_uring_ring.entries, &p->ring, &attr->io_uring_ring.params);
  if (r < 0)
  {
    (void)monad_async_executor_destroy(*ex);
    return monad_async_make_failure(-r);
  }
  if (attr->io_uring_wr_ring.entries > 0)
  {
    r = io_uring_queue_init_params(attr->io_uring_wr_ring.entries, &p->wr_ring, &attr->io_uring_wr_ring.params);
    if (r < 0)
    {
      (void)monad_async_executor_destroy(*ex);
      return monad_async_make_failure(-r);
    }
  }
  if (!(p->ring.features & IORING_FEAT_NODROP))
  {
    fprintf(stderr, "FATAL: This kernel's io_uring implementation does not implement no-drop.\n");
    abort();
  }
  if (!(p->ring.features & IORING_FEAT_SUBMIT_STABLE))
  {
    fprintf(stderr, "FATAL: This kernel's io_uring implementation does not implement stable submits.\n");
    abort();
  }
  *ex = (monad_async_executor)p;
  return monad_async_make_success(0);
}

monad_async_result monad_async_executor_destroy(monad_async_executor ex_)
{
  struct monad_async_executor_impl *ex = (struct monad_async_executor_impl *)ex_;
  if (!thrd_equal(thrd_current(), ex->owning_thread))
  {
    fprintf(stderr, "FATAL: You must destroy an executor from the same kernel thread which owns it.\n");
    abort();
  }
  if (ex->wr_ring.ring_fd != 0)
  {
    io_uring_queue_exit(&ex->wr_ring);
  }
  io_uring_queue_exit(&ex->ring);
  free(ex);
  return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_run_impl(struct monad_async_executor_impl *ex, size_t max_items, struct timespec *timeout)
{
  LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
  size_t tasks_pending_launch_count = 0;
  memset(&tasks_pending_launch, 0, sizeof(tasks_pending_launch));
  if (atomic_load_explicit((atomic_size_t *)&ex->head.tasks_pending_launch, memory_order_acquire) > 0)
  {
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(&ex->lock, &expected, 1, memory_order_acq_rel, memory_order_relaxed))
    {
      thrd_yield();
    }
    for (bool done = false; !done;)
    {
      done = true;
      for (int n = 0; n < monad_async_priority_max; n++)
      {
        if (ex->tasks_pending_launch[n].count > 0)
        {
          struct monad_async_task_impl *const task = ex->tasks_pending_launch[n].front;
          LIST_REMOVE(ex->tasks_pending_launch[n], task, &ex->head.tasks_pending_launch);
          LIST_APPEND(tasks_pending_launch[task->head.priority.cpu], task, &tasks_pending_launch_count);
          done = false;
        }
      }
    }
    atomic_store_explicit(&ex->lock, 0, memory_order_release);
  }
  struct timespec no_waiting = {.tv_sec = 0, .tv_nsec = 0};
  if (tasks_pending_launch_count > 0)
  {
    volatile int n = 0;
    timeout = &no_waiting;
    // Set the return for suspension points
    const int resuming_from_suspension = monad_async_context_set_resumption_point(&ex->run_context, "(pending task launch)");
    (void)resuming_from_suspension;
    for (; n < monad_async_priority_max; n++)
    {
      while (tasks_pending_launch[n].count > 0)
      {
        struct monad_async_task_impl *task = tasks_pending_launch[n].front;
        LIST_REMOVE(tasks_pending_launch[n], task, (size_t *)nullptr);
        task->head.is_pending_launch = false;
        LIST_APPEND(ex->tasks_running[task->head.priority.cpu], task, &ex->head.tasks_running);
        task->head.is_running = true;
        task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
        ex->head.current_task = &task->head;
        // This may suspend, in which case we shall resume above
        monad_async_context_resume_execution(&ex->run_context, &task->context);
      }
    }
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p has launched %zu pending tasks\n", ex, tasks_pending_launch_count);
#endif
  }

  // Submit all enqueued ops, and wait for some completions
  struct io_uring_cqe *cqe = nullptr;
  bool timed_out = false;
  int r;
  if (timeout == nullptr)
  {
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p submits and waits forever due to infinite timeout\n", ex);
#endif
    r = io_uring_submit_and_wait(&ex->ring, 1);
    if (r < 0)
    {
      return monad_async_make_failure(-r);
    }
    r = io_uring_peek_cqe(&ex->ring, &cqe);
  }
  else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0)
  {
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p submits and does not wait due to zero timeout\n", ex);
#endif
    r = io_uring_submit(&ex->ring);
    if (r < 0)
    {
      return monad_async_make_failure(-r);
    }
    r = io_uring_peek_cqe(&ex->ring, &cqe);
  }
  else
  {
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p submits and waits for a non-infinite timeout %ld-%ld\n", ex, timeout->tv_sec, timeout->tv_nsec);
#endif
    if (ex->ring.features & IORING_FEAT_EXT_ARG)
    {
      r = io_uring_submit(&ex->ring);
    }
    if (r < 0)
    {
      return monad_async_make_failure(-r);
    }
    r = io_uring_wait_cqe_timeout(&ex->ring, &cqe, (struct __kernel_timespec *)timeout);
  }
  if (r < 0)
  {
    if (r == -ETIME)
    {
      timed_out = true;
    }
    else if (r == -EAGAIN)
    {
      // temporary failure, ignore it
    }
    else
    {
      return monad_async_make_failure(-r);
    }
  }
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Executor %p sees cqe=%p from io_uring wait\n", ex, cqe);
#endif
  // Always empty the completions queue.
  unsigned head;
  volatile size_t i = 0;
  io_uring_for_each_cqe(&ex->ring, head, cqe)
  {
    i++;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)io_uring_cqe_get_data(cqe);
    task->head.ticks_when_suspended_completed = get_ticks_count(memory_order_relaxed);
    if (cqe->res < 0)
    {
      task->head.result = monad_async_make_failure(-cqe->res);
    }
    else
    {
      task->head.result = monad_async_make_success(cqe->res);
    }
    assert(task->head.is_suspended_awaiting);
    task->head.is_suspended_awaiting = false;
    LIST_REMOVE(ex->tasks_suspended_awaiting[task->head.priority.cpu], task, (size_t *)nullptr);
    task->head.is_suspended_completed = true;
    LIST_APPEND(ex->tasks_suspended_completed[task->head.priority.cpu], task, (size_t *)nullptr);
  }
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Executor %p has dequeued %zu completions from io_uring\n", ex, i);
#endif
  io_uring_cq_advance(&ex->ring, i);

  i = 0;
  if (max_items > 0)
  {
    // Set the return for suspension points.
    volatile int n = 0;
    const int resuming_from_suspension = monad_async_context_set_resumption_point(&ex->run_context, "(i/o completions)");
    (void)resuming_from_suspension;
    for (; n < monad_async_priority_max; n++)
    {
      while (ex->tasks_suspended_completed[n].count > 0)
      {
        if (i++ >= max_items)
        {
          break;
        }
        // Resume execution of the task. If it suspends on another operation, or exits,
        // the loop will resume iterating above.
        monad_async_context_resume_execution(&ex->run_context, &ex->tasks_suspended_completed[n].front->context);
      }
    }
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p has notified %zu tasks of i/o completion by resumption\n", ex, i);
#endif
  }
  size_t items_processed = tasks_pending_launch_count + i;
  if (items_processed > 0)
  {
    return monad_async_make_success(items_processed);
  }
  return timed_out ? monad_async_make_failure(ETIME) : monad_async_make_success(0);
}

monad_async_result monad_async_executor_run(monad_async_executor ex_, size_t max_items, struct timespec *timeout)
{
  struct monad_async_executor_impl *ex = (struct monad_async_executor_impl *)ex_;
#ifndef NDEBUG
  if (!thrd_equal(thrd_current(), ex->owning_thread))
  {
    fprintf(stderr, "FATAL: You must run an executor from the same kernel thread on which it was created.\n");
    abort();
  }
#endif
  if (ex->within_run)
  {
    fprintf(stderr, "FATAL: You must never run an executor which is already running (i.e. recursing into the executor is forbidden).\n");
    abort();
  }
  ex->within_run = true;
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Executor %p enters run\n", ex);
#endif
  monad_async_result ret = monad_async_executor_run_impl(ex, max_items, timeout);
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Executor %p exits run having processed %zu items\n", ex, ret.value);
#endif
  ex->within_run = false;
  ex->head.current_task = nullptr;
  return ret;
}

static monad_async_result monad_async_executor_suspend_impl(struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
  assert(task->head.is_running);
  assert(ex->head.current_task == &task->head);
  ex->head.current_task = nullptr;
  task->head.is_running = false;
  LIST_REMOVE(ex->tasks_running[task->head.priority.cpu], task, &ex->head.tasks_running);
  task->head.is_suspended_awaiting = true;
  LIST_APPEND(ex->tasks_suspended_awaiting[task->head.priority.cpu], task, &ex->head.tasks_suspended);
  task->head.ticks_when_suspended_awaiting = get_ticks_count(memory_order_relaxed);
  task->head.total_ticks_executed += task->head.ticks_when_suspended_awaiting - task->head.ticks_when_resumed;
  if (!monad_async_context_set_resumption_point(&task->context, "(i/o suspension)"))
  {
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf("*** Executor %p suspends task %p\n", ex, task);
#endif
    monad_async_context_resume_execution(&task->context, &ex->run_context);
  }
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Executor %p resumes task %p\n", ex, task);
#endif
  task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
  assert(!task->head.is_suspended_awaiting);
  assert(task->head.is_suspended_completed);
  task->head.is_suspended_completed = false;
  LIST_REMOVE(ex->tasks_suspended_completed[task->head.priority.cpu], task, &ex->head.tasks_suspended);
  task->head.is_running = true;
  LIST_APPEND(ex->tasks_running[task->head.priority.cpu], task, &ex->head.tasks_running);
  assert(ex->head.current_task == nullptr);
  ex->head.current_task = &task->head;
  return task->head.result;
}

struct context *monad_async_executor_task_exited(monad_async_task task_)
{
  struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
  assert(task_->is_running);
  struct monad_async_executor_impl *ex = (struct monad_async_executor_impl *)task->head.current_executor;
  assert(ex->head.current_task == task_);
  task_->ticks_when_detached = get_ticks_count(memory_order_relaxed);
  task_->total_ticks_executed += task_->ticks_when_detached - task_->ticks_when_resumed;
  task_->is_running = false;
  task_->current_executor = nullptr;
  LIST_REMOVE(ex->tasks_running[task->head.priority.cpu], task, &ex->head.tasks_running);
  // Have task return itself to freshly constructed, and return execution to the executor
  return &ex->run_context;
}

monad_async_result monad_async_task_attach(monad_async_executor ex_, monad_async_task task_)
{
  struct monad_async_executor_impl *ex = (struct monad_async_executor_impl *)ex_;
  struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
  if (task->head.user_code == nullptr)
  {
    return monad_async_make_failure(EINVAL);
  }
  if (task->head.current_executor != nullptr)
  {
#ifndef NDEBUG
    if (!thrd_equal(thrd_current(), ex->owning_thread))
    {
      fprintf(stderr, "FATAL: You must detach a task on the same kernel thread on which its executor is run.\n");
      abort();
    }
#endif
    if (task->head.is_pending_launch)
    {
      LIST_REMOVE(ex->tasks_pending_launch[task->head.pending_launch_queue_], task, &ex->head.tasks_pending_launch);
      task->head.is_pending_launch = false;
    }
    else if (task->head.is_running)
    {
      LIST_REMOVE(ex->tasks_running[task->head.priority.cpu], task, &ex->head.tasks_running);
      task->head.is_running = false;
    }
    else if (task->head.is_suspended_awaiting)
    {
      LIST_REMOVE(ex->tasks_suspended_awaiting[task->head.priority.cpu], task, &ex->head.tasks_suspended);
      task->head.is_suspended_awaiting = false;
    }
    else if (task->head.is_suspended_completed)
    {
      LIST_REMOVE(ex->tasks_suspended_completed[task->head.priority.cpu], task, &ex->head.tasks_suspended);
      task->head.is_suspended_completed = false;
    }
  }
  task->head.current_executor = (monad_async_executor)ex;
  task->head.is_pending_launch = true;
  task->head.ticks_when_attached = get_ticks_count(memory_order_relaxed);
  task->head.ticks_when_detached = 0;
  task->head.ticks_when_resumed = 0;
  task->head.ticks_when_suspended_awaiting = 0;
  task->head.ticks_when_suspended_completed = 0;
  task->head.total_ticks_executed = 0;
  int expected = 0;
  while (!atomic_compare_exchange_strong_explicit(&ex->lock, &expected, 1, memory_order_acq_rel, memory_order_relaxed))
  {
    thrd_yield();
  }
  LIST_APPEND(ex->tasks_pending_launch[ex->tasks_pending_launch_next_queue], task, &ex->head.tasks_pending_launch);
  if (++ex->tasks_pending_launch_next_queue == monad_async_priority_max)
  {
    ex->tasks_pending_launch_next_queue = 0;
  }
  atomic_store_explicit(&ex->lock, 0, memory_order_release);
  return monad_async_make_success(0);
}

monad_async_result monad_async_task_suspend_for_duration(monad_async_task task_, uint64_t ns)
{
  struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
  if (task_->current_executor == nullptr || task_->current_executor->current_task != task_)
  {
    fprintf(stderr, "FATAL: Task execution suspension invoked not by the current task executing.\n");
    abort();
  }
  struct monad_async_executor_impl *ex = (struct monad_async_executor_impl *)task_->current_executor;
  assert(ex->within_run == true);
  struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->ring);
  if (sqe == nullptr)
  {
    fprintf(stderr, "TODO: Handle SQE exhaustation via suspend until free SQE entries appear.\n");
    abort();
  }
  if (ns == 0)
  {
    io_uring_prep_nop(sqe);
  }
  else
  {
    struct __kernel_timespec ts = {.tv_sec = ns / 1000000000, .tv_nsec = ns % 1000000000};
    io_uring_prep_timeout(sqe, &ts, 1, IORING_TIMEOUT_BOOTTIME);
  }
  switch (task_->priority.io)
  {
  default:
    break;
  case monad_async_priority_high:
    sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
    break;
  case monad_async_priority_low:
    sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
    break;
  }
  io_uring_sqe_set_data(sqe, task);
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Task %p running on executor %p initiates suspend_for_duration\n", task, ex);
#endif
  monad_async_result ret = monad_async_executor_suspend_impl(ex, task);
#if MONAD_ASYNC_EXECUTOR_PRINTING
  printf("*** Task %p running on executor %p completes suspend_for_duration\n", task, ex);
#endif
  if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret))
  {
    if (ret.error.value == ETIME && ns > 0)
    {
      // io_uring returns timeouts as failure with ETIME, so filter those out
      return monad_async_make_success(0);
    }
    return ret;
  }
  return monad_async_make_success(0);
}
