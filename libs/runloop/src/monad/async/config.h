#pragma once

#include "boost_result.h"

#ifndef __clang__
    #if defined(__SANITIZE_ADDRESS__)
        #define MONAD_ASYNC_HAVE_ASAN 1
    #elif defined(__SANITIZE_THREAD__)
        #define MONAD_ASYNC_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_ASYNC_HAVE_UBSAN 1
    #endif
#else
    #if __has_feature(address_sanitizer)
        #define MONAD_ASYNC_HAVE_ASAN 1
    #elif __has_feature(thread_sanitizer)
        #define MONAD_ASYNC_HAVE_TSAN 1
    #elif defined(__SANITIZE_UNDEFINED__)
        #define MONAD_ASYNC_HAVE_UBSAN 1
    #endif
#endif

#ifndef MONAD_ASYNC_PUBLIC_CONST
    #ifdef MONAD_ASYNC_SOURCE
        #define MONAD_ASYNC_PUBLIC_CONST
    #else
        #define MONAD_ASYNC_PUBLIC_CONST const
    #endif
#endif

#ifndef MONAD_ASYNC_CPP_STD
    #ifdef __cplusplus
        #define MONAD_ASYNC_CPP_STD std::
    #else
        #define MONAD_ASYNC_CPP_STD
    #endif
#endif

#ifndef MONAD_ASYNC_ATOMIC
    #ifdef __cplusplus
        #define MONAD_ASYNC_ATOMIC(x) std::atomic<x>
    #else
        #define MONAD_ASYNC_ATOMIC(x) _Atomic x
    #endif
#endif

//! \brief Declare a Boost.Outcome layout compatible C result type for
//! `result<intptr_t>`
BOOST_OUTCOME_C_DECLARE_RESULT_SYSTEM(monad_async, intptr_t)

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief Convenience typedef
typedef BOOST_OUTCOME_C_RESULT_SYSTEM(monad_async) monad_async_result;

//! \brief Return a successful `monad_async_result` for a given `intptr_t`
BOOST_OUTCOME_C_NODISCARD extern BOOST_OUTCOME_C_WEAK monad_async_result
monad_async_make_success(intptr_t v)
{
    return BOOST_OUTCOME_C_MAKE_RESULT_SYSTEM_SUCCESS(monad_async, v);
}

//! \brief Return a failure `monad_async_result` for a given `errno`
BOOST_OUTCOME_C_NODISCARD extern BOOST_OUTCOME_C_WEAK monad_async_result
monad_async_make_failure(int ec)
{
    return BOOST_OUTCOME_C_MAKE_RESULT_SYSTEM_FAILURE_SYSTEM(monad_async, ec);
}

//! \brief A type representing the tick count on the CPU
typedef uint64_t monad_async_cpu_ticks_count_t;

#define MONAD_ASYNC_CHECK_RESULT2(unique, ...)                                 \
    {                                                                          \
        auto unique = (__VA_ARGS__);                                           \
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(unique)) {                        \
            fprintf(                                                           \
                stderr,                                                        \
                "FATAL: %s\n",                                                 \
                outcome_status_code_message(&unique.error));                   \
            abort();                                                           \
        }                                                                      \
    }
#define MONAD_ASYNC_CHECK_RESULT(...)                                          \
    MONAD_ASYNC_CHECK_RESULT2(BOOST_OUTCOME_TRY_UNIQUE_NAME, __VA_ARGS__)

//! \brief Task priority classes
typedef enum monad_async_priority
    : unsigned char
{
    monad_async_priority_high = 0,
    monad_async_priority_normal = 1,
    monad_async_priority_low = 2,

    monad_async_priority_max = 3,
    monad_async_priority_unchanged = (unsigned char)-1
} monad_async_priority;
#ifdef __cplusplus
}
#endif
