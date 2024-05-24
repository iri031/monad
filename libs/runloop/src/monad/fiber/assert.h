#pragma once

#include <assert.h>
#include <stdlib.h>

#if defined(NDEBUG)
    #define MONAD_ASSERT(expr)                                                 \
        if (!(expr)) {                                                         \
            fprintf(                                                           \
                stderr,                                                        \
                "%s(%d) [%s] Assertion failed " #expr "\n",                    \
                __FILE__,                                                      \
                __LINE__,                                                      \
                __func__);                                                     \
            exit(EXIT_FAILURE);                                                \
        }

#else
    #define MONAD_ASSERT(Expression) assert(Expression)
#endif
#define MONAD_DEBUG_ASSERT(Expression) assert(Expression)
#define MONAD_CCALL_ASSERT(Expression)                                         \
    {                                                                          \
        int _return_value_ = Expression;                                       \
        (void)_return_value_;                                                  \
        MONAD_ASSERT(!_return_value_);                                         \
    }
