#include <gtest/gtest.h>

#include "monad/async/executor.h"

#include "monad/async/cpp_helpers.hpp"
#include "monad/async/task.h"

#include <utility>
#include <stdexcept>
#include <sstream>
#include <cstdio>
#include <cstdlib>
#include <cstdint>

using namespace monad::async;
#define CHECK_RESULT2(unique, ...)                \
  {                                               \
    auto unique = (__VA_ARGS__);                  \
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(unique)) \
    {                                             \
      throw_exception(unique);                    \
    }                                             \
  }
#define CHECK_RESULT(...) CHECK_RESULT2(MONAD_ASYNC_UNIQUE_NAME, __VA_ARGS__)

TEST(async_result, works)
{
  auto r = monad_async_make_success(EINVAL);
  CHECK_RESULT(r);
  try
  {
    r = monad_async_make_failure(EINVAL);
    CHECK_RESULT(r);
  }
  catch (const std::exception &e)
  {
    EXPECT_STREQ(e.what(), "Invalid argument");
  }
}

TEST(executor, works)
{
  monad_async_executor_attr ex_attr{};
  ex_attr.io_uring_ring.entries = 64;
  auto ex = make_executor(ex_attr);
  struct timespec ts
  {
    0, 0
  };
  auto r = monad_async_executor_run(ex.get(), 1, &ts);
  try
  {
    CHECK_RESULT(r);
  }
  catch (const std::exception &e)
  {
    EXPECT_STREQ(e.what(), "Timer expired");
  }
  monad_async_task_attr t_attr{};
  {
    auto t1 = make_task(t_attr);
    bool did_run = false;
    t1->user_ptr = (void *)&did_run;
    t1->user_code = +[](monad_async_task task) -> monad_async_result
    {
      *(bool *)task->user_ptr = true;
      EXPECT_EQ(task->current_executor->current_task, task);
      EXPECT_EQ(task->current_executor->tasks_pending_launch, 0);
      EXPECT_EQ(task->current_executor->tasks_running, 1);
      EXPECT_EQ(task->current_executor->tasks_suspended, 0);
      return monad_async_make_success(5);
    };
    r = monad_async_task_attach(ex.get(), t1.get());
    CHECK_RESULT(r);
    EXPECT_TRUE(t1->is_pending_launch);
    EXPECT_FALSE(t1->is_running);
    EXPECT_FALSE(t1->is_suspended_awaiting);
    EXPECT_FALSE(t1->is_suspended_completed);
    EXPECT_EQ(ex->current_task, nullptr);
    EXPECT_EQ(ex->tasks_pending_launch, 1);
    EXPECT_EQ(ex->tasks_running, 0);
    EXPECT_EQ(ex->tasks_suspended, 0);
    r = monad_async_executor_run(ex.get(), 1, &ts);
    EXPECT_EQ(ex->tasks_pending_launch, 0);
    EXPECT_EQ(ex->tasks_running, 0);
    EXPECT_EQ(ex->tasks_suspended, 0);
    CHECK_RESULT(r);
    EXPECT_EQ(r.value, 1);
    EXPECT_FALSE(t1->is_pending_launch);
    EXPECT_FALSE(t1->is_running);
    EXPECT_FALSE(t1->is_suspended_awaiting);
    EXPECT_FALSE(t1->is_suspended_completed);
    CHECK_RESULT(t1->result);
    EXPECT_EQ(t1->result.value, 5);
    EXPECT_TRUE(did_run);
    std::cout << "   Task attach to task initiate took " << (t1->ticks_when_resumed - t1->ticks_when_attached) << " ticks.";
    std::cout << "\n   Task initiate to task detach took " << (t1->ticks_when_detached - t1->ticks_when_resumed) << " ticks.";
    std::cout << "\n   Task executed for a total of " << t1->total_ticks_executed << " ticks." << std::endl;
  }
  {
    auto t1 = make_task(t_attr);
    bool did_run = false;
    t1->user_ptr = (void *)&did_run;
    t1->user_code = +[](monad_async_task task) -> monad_async_result
    {
      *(bool *)task->user_ptr = true;
      EXPECT_EQ(task->current_executor->current_task, task);
      EXPECT_EQ(task->current_executor->tasks_pending_launch, 0);
      EXPECT_EQ(task->current_executor->tasks_running, 1);
      EXPECT_EQ(task->current_executor->tasks_suspended, 0);
      CHECK_RESULT(monad_async_task_suspend_for_duration(task, 1000000)); // one millisecond
      EXPECT_EQ(task->current_executor->current_task, task);
      EXPECT_EQ(task->current_executor->tasks_pending_launch, 0);
      EXPECT_EQ(task->current_executor->tasks_running, 1);
      EXPECT_EQ(task->current_executor->tasks_suspended, 0);
      return monad_async_make_success(5);
    };
    r = monad_async_task_attach(ex.get(), t1.get());
    CHECK_RESULT(r);
    EXPECT_TRUE(t1->is_pending_launch);
    EXPECT_FALSE(t1->is_running);
    EXPECT_FALSE(t1->is_suspended_awaiting);
    EXPECT_FALSE(t1->is_suspended_completed);
    EXPECT_EQ(ex->current_task, nullptr);
    EXPECT_EQ(ex->tasks_pending_launch, 1);
    EXPECT_EQ(ex->tasks_running, 0);
    EXPECT_EQ(ex->tasks_suspended, 0);
    ts.tv_sec = 3;                                  // timeout and fail the test after this
    r = monad_async_executor_run(ex.get(), 1, &ts); // runs and suspends
    const monad_async_cpu_ticks_count_t ticks_when_resumed = t1->ticks_when_resumed;
    EXPECT_EQ(ex->tasks_pending_launch, 0);
    EXPECT_EQ(ex->tasks_running, 0);
    EXPECT_EQ(ex->tasks_suspended, 1);
    CHECK_RESULT(r);
    EXPECT_EQ(r.value, 1);
    EXPECT_TRUE(did_run);
    EXPECT_FALSE(t1->is_pending_launch);
    EXPECT_FALSE(t1->is_running);
    EXPECT_TRUE(t1->is_suspended_awaiting);
    EXPECT_FALSE(t1->is_suspended_completed);
    r = monad_async_executor_run(ex.get(), 1, &ts); // resumes and exits
    EXPECT_EQ(ex->tasks_pending_launch, 0);
    EXPECT_EQ(ex->tasks_running, 0);
    EXPECT_EQ(ex->tasks_suspended, 0);
    CHECK_RESULT(r);
    EXPECT_EQ(r.value, 1);
    EXPECT_FALSE(t1->is_pending_launch);
    EXPECT_FALSE(t1->is_running);
    EXPECT_FALSE(t1->is_suspended_awaiting);
    EXPECT_FALSE(t1->is_suspended_completed);
    CHECK_RESULT(t1->result);
    EXPECT_EQ(t1->result.value, 5);
    EXPECT_TRUE(did_run);
    std::cout << "\n   Task attach to task initiate took " << (ticks_when_resumed - t1->ticks_when_attached) << " ticks.";
    std::cout << "\n   Task initiate to task suspend await took " << (t1->ticks_when_suspended_awaiting - ticks_when_resumed) << " ticks.";
    std::cout << "\n   Task suspend await to task suspend completed took " << (t1->ticks_when_suspended_completed - t1->ticks_when_suspended_awaiting) << " ticks.";
    std::cout << "\n   Task suspend completed to task resume took " << (t1->ticks_when_resumed - t1->ticks_when_suspended_completed) << " ticks.";
    std::cout << "\n   Task resume to task detach took " << (t1->ticks_when_detached - t1->ticks_when_resumed) << " ticks.";
    std::cout << "\n   Task executed for a total of " << t1->total_ticks_executed << " ticks." << std::endl;
  }

  {
    struct shared_t
    {
      uint64_t ops{0};
    } shared;
    auto func = +[](monad_async_task task) -> monad_async_result
    {
      auto *shared = (shared_t *)task->user_ptr;
      shared->ops++;
      return monad_async_make_success(0);
    };
    std::vector<task_ptr> tasks;
    tasks.reserve(1024);
    for (size_t n = 0; n < 1024; n++)
    {
      tasks.push_back(make_task(t_attr));
      tasks.back()->user_code = func;
      tasks.back()->user_ptr = (void *)&shared;
    }
    const auto begin = std::chrono::steady_clock::now();
    do
    {
      for (auto &i : tasks)
      {
        auto r = monad_async_task_attach(ex.get(), i.get());
        CHECK_RESULT(r);
      }
      auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
      CHECK_RESULT(r);
      if (r.value != 1024)
      {
        abort();
      }
    } while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(3));
    const auto end = std::chrono::steady_clock::now();
    std::cout << "\n\n   Initiated, executed and tore down "
              << (1000.0 * double(shared.ops) / double(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count()))
              << " ops/sec which is "
              << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / double(shared.ops)) << " ns/op." << std::endl;
  }

  {
    struct shared_t
    {
      uint64_t ops{0};
      bool done;
    } shared;
    auto func = +[](monad_async_task task) -> monad_async_result
    {
      auto *shared = (shared_t *)task->user_ptr;
      while (!shared->done)
      {
        shared->ops++;
        auto r = monad_async_task_suspend_for_duration(task, 0);
        CHECK_RESULT(r);
      }
      return monad_async_make_success(0);
    };
    std::vector<task_ptr> tasks;
    tasks.reserve(64);
    for (size_t n = 0; n < 64; n++)
    {
      tasks.push_back(make_task(t_attr));
      tasks.back()->user_code = func;
      tasks.back()->user_ptr = (void *)&shared;
      auto r = monad_async_task_attach(ex.get(), tasks.back().get());
      CHECK_RESULT(r);
    }
    const auto begin = std::chrono::steady_clock::now();
    do
    {
      auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
      CHECK_RESULT(r);
    } while (std::chrono::steady_clock::now() - begin < std::chrono::seconds(3));
    const auto end = std::chrono::steady_clock::now();
    shared.done = true;
    while (ex->tasks_running > 0)
    {
      auto r = monad_async_executor_run(ex.get(), size_t(-1), nullptr);
      CHECK_RESULT(r);
    }
    std::cout << "\n\n   Suspend-resume "
              << (1000.0 * double(shared.ops) / double(std::chrono::duration_cast<std::chrono::milliseconds>(end - begin).count()))
              << " ops/sec which is "
              << (double(std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count()) / double(shared.ops)) << " ns/op." << std::endl;
  }
}
