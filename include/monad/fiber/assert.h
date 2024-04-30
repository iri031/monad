#pragma once

#include <assert.h>

#define MONAD_ASSERT(Expression) assert(Expression)
#define MONAD_CCALL_ASSERT(Expression) {int _return_value_ = Expression; MONAD_ASSERT(!_return_value_); }
