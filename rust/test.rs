#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!{"async_with_rust_helpers.rs"}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_executor_works() {
    {
      let mut ex_attr = monad_async_executor_attr{..Default::default()};
      ex_attr.io_uring_ring.entries = 64;
      let ex = monad_async_executor_ptr::new(&mut ex_attr).unwrap();
      println!("ex = {:?}", ex);
      println!("ex->tasks_running = {}", unsafe { (*ex.head).tasks_running });

      let test = | _switcher: &monad_async_context_switcher_ptr,
                   _desc: &str| {
/*          static size_t n;
          monad_async_task_attr t_attr{};
          struct timespec ts
          {
              0, 0
          };
          std::cout << "\n\n   With " << desc << " context switcher ..."
                    << std::endl;
          for (n = 0; n < 10; n++) {
              auto t1 = make_task(switcher, t_attr);
              int did_run = 0;
              t1->user_ptr = (void *)&did_run;
              t1->user_code =
                  +[](monad_async_task task) -> monad_async_result {
                  *(int *)task->user_ptr = 1;
                  auto *current_executor =
                      task->current_executor.load(std::memory_order_acquire);
                  EXPECT_EQ(current_executor->current_task, task);
                  EXPECT_EQ(current_executor->tasks_pending_launch, 0);
                  EXPECT_EQ(current_executor->tasks_running, 1);
                  EXPECT_EQ(current_executor->tasks_suspended, 0);
                  CHECK_RESULT(monad_async_task_suspend_for_duration(
                      nullptr, task, 10000000ULL)); // 10 milliseconds
                  *(int *)task->user_ptr = 2;
                  current_executor =
                      task->current_executor.load(std::memory_order_acquire);
                  EXPECT_EQ(current_executor->current_task, task);
                  EXPECT_EQ(current_executor->tasks_pending_launch, 0);
                  EXPECT_EQ(current_executor->tasks_running, 1);
                  EXPECT_EQ(current_executor->tasks_suspended, 0);
                  return monad_async_make_success(5);
              };
              auto const suspend_begins = std::chrono::steady_clock::now();
              auto r = monad_async_task_attach(ex.get(), t1.get(), nullptr);
              CHECK_RESULT(r);
              EXPECT_TRUE(t1->is_pending_launch);
              EXPECT_FALSE(t1->is_running);
              EXPECT_FALSE(t1->is_suspended_awaiting);
              EXPECT_FALSE(t1->is_suspended_completed);
              EXPECT_EQ(ex->current_task, nullptr);
              EXPECT_EQ(ex->tasks_pending_launch, 1);
              EXPECT_EQ(ex->tasks_running, 0);
              EXPECT_EQ(ex->tasks_suspended, 0);
              ts.tv_sec = 3; // timeout and fail the test after this
              r = monad_async_executor_run(
                  ex.get(), 1, &ts); // runs and suspends
              monad_async_cpu_ticks_count_t const ticks_when_resumed =
                  t1->ticks_when_resumed;
              EXPECT_EQ(did_run, 1);
              EXPECT_EQ(ex->tasks_pending_launch, 0);
              EXPECT_EQ(ex->tasks_running, 0);
              EXPECT_EQ(ex->tasks_suspended, 1);
              CHECK_RESULT(r);
              EXPECT_EQ(r.value, 1);
              EXPECT_FALSE(t1->is_pending_launch);
              EXPECT_FALSE(t1->is_running);
              EXPECT_TRUE(t1->is_suspended_awaiting);
              EXPECT_FALSE(t1->is_suspended_completed);
              r = monad_async_executor_run(
                  ex.get(), 1, &ts); // resumes and exits
              EXPECT_EQ(did_run, 2);
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
              if (auto diff =
                      std::chrono::steady_clock::now() - suspend_begins;
                  diff < std::chrono::milliseconds(10)) {
                  std::cout << "   NOTE: On iteration " << n << ": "
                            << std::chrono::duration_cast<
                                   std::chrono::milliseconds>(diff)
                                   .count()
                            << " milliseconds have elapsed since suspend "
                               "initiation. If it went to completed in "
                               "less than 10 milliseconds, there is "
                               "something wrong with the implementation."
                            << std::endl;
                  EXPECT_GE(diff, std::chrono::milliseconds(10));
              }
              if (n == 9) {
                  std::cout << "\n   Task attach to task initiate took "
                            << (ticks_when_resumed - t1->ticks_when_attached)
                            << " ticks.";
                  std::cout
                      << "\n   Task initiate to task suspend await took "
                      << (t1->ticks_when_suspended_awaiting -
                          ticks_when_resumed)
                      << " ticks.";
                  std::cout << "\n   Task suspend await to task suspend "
                               "completed took "
                            << (t1->ticks_when_suspended_completed -
                                t1->ticks_when_suspended_awaiting)
                            << " ticks.";
                  std::cout
                      << "\n   Task suspend completed to task resume took "
                      << (t1->ticks_when_resumed -
                          t1->ticks_when_suspended_completed)
                      << " ticks.";
                  std::cout
                      << "\n   Task resume to task detach took "
                      << (t1->ticks_when_detached - t1->ticks_when_resumed)
                      << " ticks.";
                  std::cout << "\n   Task executed for a total of "
                            << t1->total_ticks_executed << " ticks."
                            << std::endl;
              }
          }
          */
      };
      let switcher = unsafe { monad_async_context_switcher_ptr::new(&monad_async_context_switcher_sjlj).unwrap() };
      test(&switcher, "setjmp/longjmp");
/*      test(
          make_context_switcher(monad_async_context_switcher_sjlj).get(),
          "setjmp/longjmp");
      test(
          make_context_switcher(monad_async_context_switcher_fiber).get(),
          "monad fiber");
          */
  }

  }

}