#include <monad/fiber/context.h>

#include <gtest/gtest.h>
#include <memory>

int test = 0;

monad_fiber_context_t *
spawn_test(void *ptr, monad_fiber_context_t *me, monad_fiber_context_t *from)
{
    EXPECT_EQ(from, monad_fiber_main_context());
    EXPECT_EQ(ptr, &test);
    test = 1;
    me = monad_fiber_context_switch(me, from);
    test = 2;
    return monad_fiber_main_context();
}

extern "C" void monad_fiber_init_main();

TEST(fiber, spawn)
{
    monad_fiber_init_main();
    test = 0;
    auto f = monad_fiber_context_callcc(
        monad_fiber_main_context(),
        monad_fiber_default_stack_size,
        false,
        &spawn_test,
        &test);
    EXPECT_EQ(test, 1);
    EXPECT_NE(f, nullptr);
    f = monad_fiber_context_switch(
        monad_fiber_main_context(), f); // complete it
    EXPECT_EQ(test, 2);
    EXPECT_EQ(f, nullptr);
}

TEST(fiber, spawn_protected)
{
    monad_fiber_init_main();
    test = 0;
    auto f = monad_fiber_context_callcc(
        monad_fiber_main_context(),
        monad_fiber_default_stack_size,
        true,
        &spawn_test,
        &test);
    EXPECT_EQ(test, 1);
    EXPECT_NE(f, nullptr);
    monad_fiber_set_name(f, "test-fiber");
    EXPECT_EQ(f->name, std::string("test-fiber"));
    f = monad_fiber_context_switch(monad_fiber_main_context(), f);
    EXPECT_EQ(test, 2);
    EXPECT_EQ(f, nullptr);
}
