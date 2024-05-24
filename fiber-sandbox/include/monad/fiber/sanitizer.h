#pragma once

#include <stddef.h>

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
    #endif

#endif
#if defined(__cplusplus)
extern "C"
{
#endif
#if defined(MONAD_USE_ASAN)

extern void __sanitizer_start_switch_fiber(
    void **fake_stack_save, void const *bottom, size_t size);

extern void __sanitizer_finish_switch_fiber(
    void *fake_stack_save, void const **bottom_old, size_t *size_old);

#endif

#if defined(MONAD_USE_TSAN)

extern void *__tsan_get_current_fiber(void);
extern void *__tsan_create_fiber(unsigned flags);
extern void __tsan_destroy_fiber(void *fiber);
extern void __tsan_switch_to_fiber(void *fiber, unsigned flags);
extern void __tsan_set_fiber_name(void *fiber, char const *name);

#endif

#if defined(__cplusplus)
}
#endif
