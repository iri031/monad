#pragma once

#include "executor.h"
#include "task.h"

#include <memory>

namespace monad
{
  namespace async
  {
    //! \brief Throws any error in the result as a C++ exception
    [[noreturn]] extern void throw_exception(monad_async_result r);

    struct executor_deleter
    {
      void operator()(monad_async_executor ex) const
      {
        auto r = ::monad_async_executor_destroy(ex);
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r))
        {
          throw_exception(r);
        }
      }
    };
    using executor_ptr = std::unique_ptr<monad_async_executor_head, executor_deleter>;

    struct task_deleter
    {
      void operator()(monad_async_task t) const
      {
        auto r = ::monad_async_task_destroy(t);
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r))
        {
          throw_exception(r);
        }
      }
    };
    using task_ptr = std::unique_ptr<monad_async_task_head, task_deleter>;

    //! \brief Construct an executor instance, and return it in a smart pointer
    executor_ptr make_executor(struct monad_async_executor_attr &attr)
    {
      monad_async_executor ex;
      auto r = monad_async_executor_create(&ex, &attr);
      if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r))
      {
        throw_exception(r);
      }
      return executor_ptr(ex);
    }

    //! \brief Construct a task instance, and return it in a smart pointer
    task_ptr make_task(struct monad_async_task_attr &attr)
    {
      monad_async_task t;
      auto r = monad_async_task_create(&t, &attr);
      if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r))
      {
        throw_exception(r);
      }
      return task_ptr(t);
    }
  }
}
