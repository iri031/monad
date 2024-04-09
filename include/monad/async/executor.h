#pragma once

#include "config.h"

#include "task.h"

#include <liburing.h>

#ifdef __cplusplus
extern "C"
{
#endif

  typedef struct monad_async_executor_head
  {
    monad_async_task current_task;
    size_t tasks_pending_launch;
    size_t tasks_running;
    size_t tasks_suspended;
  } *monad_async_executor;

  //! \brief Attributes by which to construct an executor
  struct monad_async_executor_attr
  {
    struct
    {
      unsigned entries;
      struct io_uring_params params;
    } io_uring_ring, io_uring_wr_ring;
  };

  //! \brief EXPENSIVE Creates an executor instance. You must create it on the kernel thread where it will be used.
  MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_create(monad_async_executor *ex, struct monad_async_executor_attr *attr);

  //! \brief EXPENSIVE Destroys an executor instance.
  MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_destroy(monad_async_executor ex);

  //! \brief Processes no more than `max_items` work items, returning the number of items processed which will be at least one.
  //! A null `timeout` means wait forever, and a zero timeout will poll without blocking.
  MONAD_ASYNC_NODISCARD extern monad_async_result monad_async_executor_run(monad_async_executor ex, size_t max_items, struct timespec *timeout);

#ifdef __cplusplus
}
#endif
