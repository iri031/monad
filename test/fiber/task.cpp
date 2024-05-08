#include <gtest/gtest.h>

#include <monad/fiber/task.h>

#include <algorithm>

TEST(task, grow)
{

  monad_fiber_task_queue_t q;
  monad_fiber_task_queue_init(&q);

  const auto cap = q.capacity;

  monad_fiber_task_queue_grow(&q);

  EXPECT_EQ(cap * 2, q.capacity);

  monad_fiber_task_queue_destroy(&q);
}

TEST(task, insert_many)
{
  monad_fiber_task_queue_t q;
  monad_fiber_task_queue_init(&q);

  const auto cap = q.capacity;
  EXPECT_EQ(cap, q.capacity);

  for (std::int64_t n = 0; n < cap; n++)
    monad_fiber_task_queue_insert(&q, (monad_fiber_task_t*)n, n);

  EXPECT_EQ(cap, q.capacity);

  for (std::int64_t n = 0; n < cap; n++)
    monad_fiber_task_queue_insert(&q, (monad_fiber_task_t*)n, n);

  EXPECT_EQ(cap  * 2, q.capacity);

  for (std::int64_t n = 0; n < cap; n++)
    monad_fiber_task_queue_insert(&q, (monad_fiber_task_t*)n, n);

  EXPECT_EQ(cap  * 3, q.capacity);


  for (std::int64_t n = 0; n < cap; n++)
    monad_fiber_task_queue_insert(&q, (monad_fiber_task_t*)n, n);

  EXPECT_EQ(cap  * 4, q.capacity);

  std::vector<std::int64_t> priorities;
  priorities.reserve(q.size);


  for (std::size_t n = 0u; n < cap; n++)
  {
    struct monad_fiber_task_node qq[4] = {
        monad_fiber_task_queue_pop_front(&q),
        monad_fiber_task_queue_pop_front(&q),
        monad_fiber_task_queue_pop_front(&q),
        monad_fiber_task_queue_pop_front(&q)
    };

    for (auto q : qq)
    {
      EXPECT_EQ(q.priority, n);
      EXPECT_EQ(q.task,  (monad_fiber_task_t*)n);
      priorities.push_back(q.priority);
    }
  }

  EXPECT_TRUE(std::is_sorted(priorities.begin(), priorities.end()));



  monad_fiber_task_queue_destroy(&q);
}


TEST(task, wrap_around)
{

  monad_fiber_task_queue_t q;
  monad_fiber_task_queue_init(&q);

  monad_fiber_task_t t1, t2, t3;

  const auto cap = static_cast<std::int64_t>(q.capacity);

  // fill the queue
  for (std::int64_t n = 0; n < cap; n++)
    monad_fiber_task_queue_insert(&q, &t1, n);

  EXPECT_EQ(cap, q.capacity);
  EXPECT_EQ(q.size, cap);

  for (std::int64_t n = 0; n < (cap / 2); n++)
  {
    auto qq = monad_fiber_task_queue_pop_front(&q);
    EXPECT_EQ(qq.priority, n);
    EXPECT_EQ(qq.task, &t1);
  }


  EXPECT_EQ(q.size, cap / 2);
  EXPECT_EQ(q.data - q.memory, cap / 2);

  for (std::int64_t n = 0; n < (cap / 4); n++) // push some to the front
    monad_fiber_task_queue_insert(&q, &t2, n);

  EXPECT_EQ(q.size, cap * 3 / 4);
  EXPECT_EQ(cap, q.capacity);

  for (std::int64_t n = 0; n < (cap / 4); n++) // push some to the end
    monad_fiber_task_queue_insert(&q, &t3, n + cap);

  EXPECT_EQ(cap, q.capacity);

  // ok, now:
  EXPECT_EQ(q.size, q.capacity); //is full!
  EXPECT_EQ(q.data->priority, 0u);


  std::vector<std::int64_t> priorities;
  priorities.reserve(q.size);

  for (std::int64_t n = 0; n < (cap / 4); n++)
  {
    auto qq = monad_fiber_task_queue_pop_front(&q);
    EXPECT_EQ(qq.priority, n);
    EXPECT_EQ(qq.task , &t2);
    priorities.push_back(qq.priority);
  }

  for (std::int64_t n = 0; n < (cap / 2); n++)
  {
    auto qq = monad_fiber_task_queue_pop_front(&q);
    EXPECT_EQ(qq.priority, n + (cap / 2));
    EXPECT_EQ(qq.task , &t1);
    priorities.push_back(qq.priority);
  }

  for (std::int64_t n = 0; n < (cap / 4); n++)
  {
    auto qq = monad_fiber_task_queue_pop_front(&q);
    EXPECT_EQ(qq.priority, n + cap);
    EXPECT_EQ(qq.task , &t3);
    priorities.push_back(qq.priority);
  }


  EXPECT_TRUE(std::is_sorted(priorities.begin(), priorities.end()));

  monad_fiber_task_queue_destroy(&q);

}
