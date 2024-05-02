
#include <gtest/gtest.h>

#include <assert.h>
#include <malloc.h>
#include <monad/fiber/fcontext.h>

int fiber_state = 0;

void fiber_impl(struct transfer_t t)
{
    EXPECT_EQ(t.data, &fiber_state);
    fiber_state++;
    t = jump_fcontext(t.fctx, &fiber_state - 1);
    EXPECT_EQ(t.data, &fiber_state + 1);
    fiber_state++;

    //  jump_fcontext(t.fctx, &fiber_state - 2);

    // unwind the fcontext
    ontop_fcontext(
        t.fctx, nullptr, +[](struct transfer_t) -> struct transfer_t {
            return {nullptr, nullptr};
        });
}

TEST(fcontext, basics)
{
    size_t const size = 4096 * 16;
    void *stack = malloc(size);

    fcontext_t f = make_fcontext((char *)stack + size, size, &fiber_impl);
    assert(fiber_state == 0);

    struct transfer_t tt = jump_fcontext(f, &fiber_state);

    EXPECT_EQ(fiber_state, 1);
    EXPECT_NE(tt.fctx, nullptr);
    EXPECT_EQ(tt.data, &fiber_state - 1);

    tt = jump_fcontext(tt.fctx, &fiber_state + 1);

    EXPECT_EQ(fiber_state, 2);
    EXPECT_EQ(tt.fctx, nullptr);
    free(stack);
}
