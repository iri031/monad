#pragma once

#if __GNUC__ && !defined(__clang__)

#if defined(__SANITIZE_ADDRESS__)
#define MONAD_USE_ASAN 1
#endif

#if defined(__SANITIZE_THREAD__)
#define MONAD_USE_TSAN 1
#endif

#elif defined(__clang__)

#if __has_feature(address_sanitizer)
#define MONAD_USE_ASAN 1
#endif

#if __has_feature(thread_sanitizer)
#define MONAD_USE_TSAN 1
#else
#error Why no tsan
#endif

#endif

#if defined(MONAD_USE_ASAN)

#include <sanitizer/asan_interface.h

#endif

#if defined(MONAD_USE_TSAN)

#include <sanitizer/tsan_interface.h>

#endif