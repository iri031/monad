
#include <gtest/gtest.h>

#include <monad/fiber/fcontext.h>
#include <malloc.h>
#include <assert.h>

int fiber_state = 0;

void fiber_impl(struct transfer_t t)
{
  EXPECT_EQ(t.data, &fiber_state);
  fiber_state++;
  t = jump_fcontext(t.fctx, &fiber_state - 1);
  EXPECT_EQ(t.data, &fiber_state);
  fiber_state++;
}

TEST(fcontext, basics)
{
  const size_t size = 4096*16;
  void * stack = malloc(size);

  fcontext_t f = make_fcontext((char*)stack + size, size, &fiber_impl);
  assert(fiber_state == 0);

  struct transfer_t tt = jump_fcontext(f , &fiber_state);

  EXPECT_EQ(fiber_state, 1);
  EXPECT_NE(tt.fctx, nullptr);
  EXPECT_EQ(tt.data, &fiber_state - 1);

  tt = jump_fcontext(f , &fiber_state + 1);

  EXPECT_EQ(fiber_state, 1);
  EXPECT_EQ(tt.fctx, nullptr);
  free(stack);
}