#include <gtest/gtest.h>


#include <monad/fiber/scheduler.h>
#include <vector>

monad_fiber_scheduler sched;
std::atomic_size_t resumed;
size_t priority = 0;

struct task : monad_fiber_task_t
{
    task() : monad_fiber_task_t{
        .resume=+[](monad_fiber_task_t * this_){static_cast<task*>(this_)->resume_();},
        .destroy=+[](monad_fiber_task_t * this_){}
    }
    {
    }

    ~task() {EXPECT_TRUE(done);}

    bool repeat = false;
    bool done = false;
    void resume_()
    {
      resumed++;
      resumed.notify_all();

      if (!repeat)
      {
        repeat = true;
        monad_fiber_scheduler_dispatch(&sched, this, priority--);
      }
      else
        done = true;

    }
};

TEST(scheduler, basics)
{
  std::vector<task> tasks{2048};
  monad_fiber_scheduler_create(&sched, 2);

  for (auto & t : tasks)
    monad_fiber_scheduler_dispatch(&sched, &t, priority--);

  for (auto r = resumed.load(); r < tasks.size() * 2; r = resumed.load())
    resumed.wait(r);

  for (auto & t : tasks)
    monad_fiber_scheduler_post(&sched, &t, priority--);

  monad_fiber_scheduler_stop(&sched);
  monad_fiber_scheduler_destroy(&sched);
}