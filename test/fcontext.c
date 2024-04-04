//
// Copyright (c) 2023 Klemens Morgenstern (klemens.morgenstern@gmx.net)
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
//

#include <monad/fiber/fcontext.h>
#include <malloc.h>
#include <assert.h>

int fiber_state = 0;

void fiber_impl(struct transfer_t t)
{
  assert(t.data == &fiber_state);
  fiber_state++;
  t = jump_fcontext(t.fctx, &fiber_state - 1);
  assert(t.data == &fiber_state);
  fiber_state++;
}

int main(int argc, char * argv[])
{
  const size_t size = 4096*16;
  void * stack = malloc(size);

  fcontext_t f = make_fcontext((char*)stack + size, size, &fiber_impl);
  assert(fiber_state == 0);

  struct transfer_t tt = jump_fcontext(f , &fiber_state);

  assert(fiber_state == 1);
  assert(tt.fctx != NULL);
  assert(tt.data == &fiber_state - 1);

  tt = jump_fcontext(f , &fiber_state + 1);

  assert(fiber_state == 1);
  assert(tt.fctx == NULL);
  free(stack);

  return 0;
}