#include <gtest/gtest.h>

#include <monad/fiber/current.h>

TEST(current, fiber_main)
{
  monad_fiber_t * mm = monad_fiber_main(), th1 = {}, th2 = {};

  std::thread{
    [&]{
      auto f = monad_fiber_main();
      th1 = *f;
      EXPECT_NE(monad_fiber_main(), mm);
      EXPECT_TRUE(monad_fiber_is_main(f));
    }}.join();
  std::thread{
    [&]{
      auto f = monad_fiber_main();
      th2 = *f;
      EXPECT_NE(monad_fiber_main(), mm);
      EXPECT_TRUE(monad_fiber_is_main(f));
    }}.join();

  EXPECT_EQ(mm->priority, th1.priority);
  EXPECT_EQ(mm->priority, th2.priority);
  EXPECT_EQ(mm->task.resume, th1.task.resume);
  EXPECT_EQ(mm->task.resume, th2.task.resume);

  EXPECT_TRUE(monad_fiber_is_main(mm));
}

extern "C" monad_fiber_t *monad_fiber_activate_fiber(monad_fiber_t *new_current);


TEST(current, switch_)
{
  monad_fiber_init_main();
  monad_fiber_t * mf = monad_fiber_main();


  monad_fiber_t mft = {
      .task = {},
      .context = nullptr,
      .priority=-1ll,
  };


  auto l =
      [&](monad_fiber_context_t * fb, monad_fiber_context_t * from) -> monad_fiber_context_t*
      {
        mft.context = fb;
        monad_fiber_set_name(fb, "switch_test_fiber");
        auto m = monad_fiber_activate_fiber(&mft);
        assert(m == monad_fiber_main());
        monad_fiber_switch_to_main();
        monad_fiber_activate_fiber(m); //preemptively go back to main.
        return from;
      };

  mft.context = monad_fiber_context_callcc(
        mf->context, 4096, false,
        +[](void * ptr, monad_fiber_context_t * fb, monad_fiber_context_t * from) -> monad_fiber_context_t *
        {
          return (*static_cast<decltype(l)*>(ptr))(fb, from);

        }, &l);

  monad_fiber_scheduler shed;
  monad_fiber_scheduler_create(&shed, 0);
  mf->scheduler = &shed;
  monad_fiber_switch_to_fiber(&mft);
  monad_fiber_scheduler_destroy(&shed);
  mf->scheduler = NULL;
}

TEST(current, yield_to_nothing)
{
  monad_fiber_t * mf = monad_fiber_main();
  monad_fiber_scheduler shed;
  monad_fiber_scheduler_create(&shed, 0);
  mf->scheduler = &shed;
  monad_fiber_yield();
  monad_fiber_scheduler_destroy(&shed);
  mf->scheduler = NULL;
}