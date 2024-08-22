#include <thread>

#include <gtest/gtest.h>

#include <monad/core/spinlock.h>

struct shared_state
{
    monad_spinlock_t lock;
    unsigned counter;
    unsigned odd_count;
    unsigned even_count;
};

constexpr unsigned ITER_MAX = 1 << 20;

static void thread_function(shared_state &s)
{
    while (true) {
        MONAD_SPINLOCK_LOCK(&s.lock);
        ASSERT_TRUE(monad_spinlock_is_owned(&s.lock));
        if (s.counter == ITER_MAX) [[unlikely]] {
            MONAD_SPINLOCK_UNLOCK(&s.lock);
            return;
        }
        if (s.counter % 2 == 0) {
            ++s.counter;
            ++s.odd_count;
        }
        MONAD_SPINLOCK_UNLOCK(&s.lock);
        std::this_thread::yield();
    }
}

TEST(spinlock, basic)
{
    shared_state s{};
    bool done;
    monad_spinlock_init(&s.lock);
    ASSERT_TRUE(monad_spinlock_is_unowned(&s.lock));

    std::thread thr{thread_function, std::ref(s)};
    do {
        MONAD_SPINLOCK_LOCK(&s.lock);
        ASSERT_TRUE(monad_spinlock_is_owned(&s.lock));
        if (s.counter % 2 == 1) {
            ++s.counter;
            ++s.even_count;
        }
        done = s.counter == ITER_MAX;
        MONAD_SPINLOCK_UNLOCK(&s.lock);
        std::this_thread::yield();
    }
    while (!done);

    thr.join();
    ASSERT_EQ(s.counter / 2, s.odd_count);
    ASSERT_EQ(s.counter / 2, s.even_count);
}
