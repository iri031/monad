#include <gtest/gtest.h>

#include <monad/fiber/task.h>

#include <algorithm>
#include <vector>

TEST(task, grow)
{

    monad_fiber_task_queue_t q;
    monad_fiber_task_queue_init(&q);

    auto const cap = q.capacity;

    monad_fiber_task_queue_grow(&q);

    EXPECT_EQ(cap * 2, q.capacity);

    monad_fiber_task_queue_destroy(&q);
}

TEST(task, insert_many)
{
    monad_fiber_task_queue_t q;
    monad_fiber_task_queue_init(&q);

    auto const cap = static_cast<std::int64_t>(q.capacity);
    EXPECT_EQ(cap, q.capacity);

    std::vector<monad_fiber_task_t> v[4];
    auto & v1 = v[0];
    v1.resize(static_cast<size_t>(cap));

    for (std::int64_t n = 0; n < cap; n++) {
        v1[static_cast<size_t>(n)].priority = n;
        monad_fiber_task_queue_insert(&q, &v1[static_cast<size_t>(n)]);
    }

    EXPECT_EQ(cap, q.capacity);

    auto & v2 = v[1];
    v2.resize(static_cast<size_t>(cap));

    for (std::int64_t n = 0; n < cap; n++) {
        v2[static_cast<size_t>(n)].priority = n;
        monad_fiber_task_queue_insert(&q, &v2[static_cast<size_t>(n)]);
    }

    EXPECT_EQ(cap * 2, q.capacity);


    auto & v3 = v[2];
    v3.resize(static_cast<size_t>(cap));

    for (std::int64_t n = 0; n < cap; n++) {
        v3[static_cast<size_t>(n)].priority = n;
        monad_fiber_task_queue_insert(&q, &v3[static_cast<size_t>(n)]);
    }

    EXPECT_EQ(cap * 3, q.capacity);

    auto & v4 = v[3];
    v4.resize(static_cast<size_t>(cap));

    for (std::int64_t n = 0; n < cap; n++) {
        v4[static_cast<size_t>(n)].priority = n;
        monad_fiber_task_queue_insert(&q, &v4[static_cast<size_t>(n)]);
    }

    EXPECT_EQ(cap * 4, q.capacity);

    std::vector<std::int64_t> priorities;
    priorities.reserve(q.size);

    for (std::int64_t n = 0; n < cap; n++) {
        monad_fiber_task_t *  qq[4] = {
            monad_fiber_task_queue_pop_front(&q),
            monad_fiber_task_queue_pop_front(&q),
            monad_fiber_task_queue_pop_front(&q),
            monad_fiber_task_queue_pop_front(&q)};

        for (auto i = 0u; i < 4u; i++)
        {
            auto & q_ = qq[i];
            EXPECT_EQ(q_->priority, n);
            EXPECT_EQ(q_, &v[i][static_cast<size_t>(n)]);
            priorities.push_back(q_->priority);
        }
    }

    EXPECT_TRUE(std::is_sorted(priorities.begin(), priorities.end()));

    monad_fiber_task_queue_destroy(&q);
}

TEST(task, wrap_around)
{

    monad_fiber_task_queue_t q;
    monad_fiber_task_queue_init(&q);

    auto const cap = static_cast<std::int64_t>(q.capacity);

    std::vector<monad_fiber_task_t> v1, v2, v3;
    v1.resize(q.capacity);
    // fill the queue
    for (std::int64_t n = 0; n < cap; n++) {
        auto & t = v1[static_cast<std::size_t>(n)];
        t.priority = n;
        monad_fiber_task_queue_insert(&q, &t);
    }

    EXPECT_EQ(cap, q.capacity);
    EXPECT_EQ(q.size, cap);

    for (std::int64_t n = 0; n < (cap / 2); n++) {
        auto qq = monad_fiber_task_queue_pop_front(&q);
        EXPECT_EQ(qq->priority, n);
        EXPECT_EQ(qq, &v1[static_cast<std::size_t>(n)]);
    }

    EXPECT_EQ(q.size, cap / 2);
    EXPECT_EQ(q.data - q.memory, cap / 2);

    v2.resize(q.capacity / 4);

    for (std::int64_t n = 0; n < (cap / 4); n++) { // push some to the front
        auto & t = v2[static_cast<std::size_t>(n)];
        t.priority = n;
        monad_fiber_task_queue_insert(&q, &t);
    }

    EXPECT_EQ(q.size, cap * 3 / 4);
    EXPECT_EQ(cap, q.capacity);

    v3.resize(q.capacity / 4);

    for (std::int64_t n = 0; n < (cap / 4); n++) { // push some to the end
        auto & t = v3[static_cast<std::size_t>(n)];
        t.priority = n + cap;
        monad_fiber_task_queue_insert(&q, &t);
    }

    EXPECT_EQ(cap, q.capacity);

    // ok, now:
    EXPECT_EQ(q.size, q.capacity); // is full!
    EXPECT_EQ((*q.data)->priority, 0u);

    std::vector<std::int64_t> priorities;
    priorities.reserve(q.size);

    for (std::int64_t n = 0; n < (cap / 4); n++) {
        auto qq = monad_fiber_task_queue_pop_front(&q);
        EXPECT_EQ(qq->priority, n);
        EXPECT_EQ(qq, &v2[static_cast<std::size_t>(n)]);
        priorities.push_back(qq->priority);
    }

    for (std::int64_t n = 0; n < (cap / 2); n++) {
        auto qq = monad_fiber_task_queue_pop_front(&q);
        EXPECT_EQ(qq->priority, n + (cap / 2));
        EXPECT_EQ(qq, &v1[static_cast<std::size_t>(n + (cap / 2))]);
        priorities.push_back(qq->priority);
    }

    for (std::int64_t n = 0; n < (cap / 4); n++) {
        auto qq = monad_fiber_task_queue_pop_front(&q);
        EXPECT_EQ(qq->priority, n + cap);
        EXPECT_EQ(qq, &v3[static_cast<std::size_t>(n)]);
        priorities.push_back(qq->priority);
    }

    EXPECT_TRUE(std::is_sorted(priorities.begin(), priorities.end()));

    monad_fiber_task_queue_destroy(&q);
}
