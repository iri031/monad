#pragma once

#include "config.h"

#include <stdlib.h>

#ifdef __cplusplus
extern "C"
{
#endif
  typedef struct monad_async_executor_head *monad_async_executor;

  typedef struct monad_async_task_head
  {
    // These can be set by the user
    struct
    {
      monad_async_priority cpu;
      monad_async_priority io;
    } priority;
    monad_async_result result;
    monad_async_result (*user_code)(struct monad_async_task_head *);
    void *user_ptr;

    // The following are not user modifiable
    bool is_pending_launch, is_running, is_suspended_awaiting, is_suspended_completed;
    monad_async_priority pending_launch_queue_;
    monad_async_executor current_executor;
    monad_async_cpu_ticks_count_t ticks_when_attached;
    monad_async_cpu_ticks_count_t ticks_when_detached;
    monad_async_cpu_ticks_count_t ticks_when_suspended_awaiting;
    monad_async_cpu_ticks_count_t ticks_when_suspended_completed;
    monad_async_cpu_ticks_count_t ticks_when_resumed;
    monad_async_cpu_ticks_count_t total_ticks_executed;
  } *monad_async_task;

  //! \brief Attributes by which to construct a task
  struct monad_async_task_attr
  {
    size_t stack_size; // 0 chooses platform default
  };

  //! \brief EXPENSIVE Creates a task instance.
  [[nodiscard]] extern monad_async_result monad_async_task_create(monad_async_task *task, struct monad_async_task_attr *attr);

  //! \brief EXPENSIVE Destroys a task instance.
  [[nodiscard]] extern monad_async_result monad_async_task_destroy(monad_async_task task);

  //! \brief THREADSAFE Attaches a task instance onto a given executor, which means it will launch the next time the executor runs.
  //! If the task is attached already to a different executor, you MUST call this function from that executor's kernel thread.
  [[nodiscard]] extern monad_async_result monad_async_task_attach(monad_async_executor executor, monad_async_task task); // implemented in executor.c

  //! \brief Suspend execution of a task for a given duration, which can be zero (which equates "yield").
  [[nodiscard]] extern monad_async_result monad_async_task_suspend_for_duration(monad_async_task task, uint64_t ns); // implemented in executor.c

#ifdef __cplusplus
}
#endif
