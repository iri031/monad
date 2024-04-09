#pragma once

// Prevent glibc stack check for longjmp
#undef _FORTIFY_SOURCE
#define _FORTIFY_SOURCE 0

// #define MONAD_ASYNC_CONTEXT_PRINTING 1

#include "monad/async/task.h"

#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>
#include <string.h>

#ifdef __cplusplus
extern "C"
{
#endif
  struct context;

  extern struct context *monad_async_executor_task_exited(monad_async_task task);

  static inline monad_async_cpu_ticks_count_t get_ticks_count(memory_order rel)
  {
    switch (rel)
    {
    case memory_order_acq_rel:
    case memory_order_acquire:
    case memory_order_release:
    case memory_order_seq_cst:
      atomic_thread_fence(rel);
      break;
    default:
      break;
    }
    monad_async_cpu_ticks_count_t ret;
#if defined(__i386__) || defined(_M_IX86) || defined(__x86_64__) || defined(_M_X64)
#if defined(__x86_64__)
    unsigned lo, hi, aux;
    asm volatile("rdtsc" : "=a"(lo), "=d"(hi), "=c"(aux));
    ret = (uint64_t)lo | ((uint64_t)hi << 32);
#elif defined(__i386__)
    unsigned lo, hi, aux;
    asm volatile("rdtsc" : "=a"(lo), "=d"(hi), "=c"(aux));
    ret = (uint64_t)lo | ((uint64_t)hi << 32);
#endif
#elif defined(__aarch64__) || defined(_M_ARM64)
#if !defined(_MSC_VER) || (defined(_MSC_VER) && defined(__clang__) && !defined(__c2__))
  uint64_t value = 0;
  __asm__ __volatile__("mrs %0, PMCCNTR_EL0" : "=r"(value)); // NOLINT
  ret = value;
#else
  uint64_t count = _ReadStatusReg(ARM64_PMCCNTR_EL0);
  ret = count;
#endif
#elif defined(__arm__) || defined(_M_ARM)
#if __ARM_ARCH >= 6 || defined(_MSC_VER)
#if !defined(_MSC_VER) || (defined(_MSC_VER) && defined(__clang__) && !defined(__c2__))
#undef _MoveFromCoprocessor
#define _MoveFromCoprocessor(coproc, opcode1, crn, crm, opcode2)                                               \
  ({                                                                                                           \
    unsigned value;                                                                                            \
    __asm__ __volatile__("MRC p" #coproc ", " #opcode1 ", %0, c" #crn ", c" #crm ", " #opcode2 : "=r"(value)); \
    value;                                                                                                     \
  }) // NOLINT
#endif
  unsigned count;
  // asm volatile("MRC p15, 0, %0, c9, c13, 0" : "=r"(count));
  count = _MoveFromCoprocessor(15, 0, 9, 13, 0);
  ret = (uint64_t)count * 64;
#endif
#else
#error "Unsupported platform"
#endif
    switch (rel)
    {
    case memory_order_acq_rel:
    case memory_order_acquire:
    case memory_order_seq_cst:
      atomic_thread_fence(rel);
      break;
    default:
      break;
    }
    return ret;
  }

#ifdef __cplusplus
}
#endif

#if 1 // temporary ucontext + setjmp based coroutine implementation

#include <setjmp.h>
#include <stdio.h>
#include <ucontext.h>
#include <sys/mman.h>
#include <unistd.h>

#if MONAD_ASYNC_HAVE_ASAN
#include <sanitizer/asan_interface.h>
#endif

#ifdef __cplusplus
extern "C"
{
#endif

  struct context
  {
    void *stack_storage;
    ucontext_t uctx;
    jmp_buf buf;

    // Sanitiser stuff
    struct
    {
      void *fake_stack_save;
      const void *bottom;
      size_t size;
    } sanitizer;
  };

#if MONAD_ASYNC_HAVE_ASAN
  static inline __attribute__((always_inline)) void start_switch_context(void **fake_stack_save,
                                                                         const void *bottom, size_t size)
  {
    __sanitizer_start_switch_fiber(fake_stack_save, bottom, size);
  }
  static inline __attribute__((always_inline)) void finish_switch_context(void *fake_stack_save,
                                                                          const void **bottom_old, size_t *size_old)
  {
    __sanitizer_finish_switch_fiber(fake_stack_save, bottom_old, size_old);
  }
#else
static inline void start_switch_context(void **, const void *, size_t)
{
}
static inline void finish_switch_context(void *, const void **, size_t *)
{
}
#endif

#if MONAD_ASYNC_CONTEXT_PRINTING
#define monad_async_context_set_resumption_point(context, desc)                                                              \
  ({                                                                                                                         \
    int _ret_ = setjmp((context)->buf);                                                                                      \
    if (_ret_ != 0)                                                                                                          \
    {                                                                                                                        \
      finish_switch_context((context)->sanitizer.fake_stack_save, &(context)->sanitizer.bottom, &(context)->sanitizer.size); \
      printf("*** Execution context %p resumes execution " desc "\n", context);                                              \
      assert((int)(uintptr_t)(context) == _ret_);                                                                            \
    }                                                                                                                        \
    printf("*** Execution context %p sets resumption point " desc "\n", context);                                            \
    _ret_;                                                                                                                   \
  })
#else
#define monad_async_context_set_resumption_point(context, desc)                                                              \
  ({                                                                                                                         \
    int _ret_ = setjmp((context)->buf);                                                                                      \
    if (_ret_ != 0)                                                                                                          \
    {                                                                                                                        \
      finish_switch_context((context)->sanitizer.fake_stack_save, &(context)->sanitizer.bottom, &(context)->sanitizer.size); \
      assert((int)(uintptr_t)(context) == _ret_);                                                                            \
    }                                                                                                                        \
    _ret_;                                                                                                                   \
  })
#endif

  static inline void monad_async_context_resume_execution(struct context *old_context, struct context *new_context)
  {
#if MONAD_ASYNC_CONTEXT_PRINTING
    printf("*** Execution context %p initiates resumption of execution in context %p\n", old_context, new_context);
#endif
    start_switch_context(&old_context->sanitizer.fake_stack_save, new_context->sanitizer.bottom, new_context->sanitizer.size);
    longjmp(new_context->buf, (int)(uintptr_t)new_context);
  }

  static void context_task_runner(struct context *context, monad_async_task task, struct context *ret)
  {
    // We are now at the base of our custom stack
    // WARNING: This custom stack will get freed without unwind
    // This is why when not in use, it sits at the setjmp in this base runner function
    //
    // TODO: We currently don't tell the sanitiser to free its resources associated with this context
    // upon deallocation. For this, we need to call:
    //
    // start_switch_context(nullptr, ret->sanitizer.bottom, ret->sanitizer.size);
    //
    // just before the final longjmp out.

#if MONAD_ASYNC_HAVE_ASAN
    // First time call fake_stack_save will be null which means no historical stack to restore for this brand new context
    assert(context->sanitizer.fake_stack_save == nullptr);
#endif
    finish_switch_context(context->sanitizer.fake_stack_save, &context->sanitizer.bottom, &context->sanitizer.size);
#if MONAD_ASYNC_CONTEXT_PRINTING
    printf("*** New execution context %p\n", context);
#endif
    for (;;)
    {
      assert(ret != nullptr);
      if (monad_async_context_set_resumption_point(context, "(base task runner awaiting new work)") == 0)
      {
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf("*** Execution context %p suspends in base task runner awaiting code to run\n", context);
#endif
        monad_async_context_resume_execution(context, ret);
      }
      ret = nullptr; // it is now dead
#if MONAD_ASYNC_CONTEXT_PRINTING
      printf("*** Execution context %p resumes in base task runner, begins executing task\n", context);
#endif
      // Execute the task
      task->result = task->user_code(task);
#if MONAD_ASYNC_CONTEXT_PRINTING
      printf("*** Execution context %p returns to base task runner, task has exited\n", context);
#endif
      ret = monad_async_executor_task_exited(task);
    }
  }

  static bool monad_async_context_init(struct context *context, monad_async_task task, const struct monad_async_task_attr *attr)
  {
    size_t stack_size = attr->stack_size;
    if (stack_size == 0)
    {
      stack_size = sysconf(_SC_THREAD_STACK_MIN);
    }
    context->stack_storage = mmap(nullptr, stack_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_GROWSDOWN | MAP_STACK, -1, 0);
    if (context->stack_storage == MAP_FAILED)
    {
      context->stack_storage = nullptr;
      return false;
    }
    // Clone the current execution context
    struct context ret;
    memset(&ret, 0, sizeof(ret));
    if (getcontext(&context->uctx) == -1)
    {
      return false;
    }
    // Replace its stack
    context->uctx.uc_stack.ss_size = stack_size;
    context->uctx.uc_stack.ss_sp = context->stack_storage;
    context->sanitizer.bottom = context->stack_storage;
    context->sanitizer.size = stack_size;
    // Launch execution, suspending immediately
    makecontext(&context->uctx, (void (*)(void))context_task_runner, 3, context, task, &ret);
    if (monad_async_context_set_resumption_point(&ret, "(monad_async_context_init)") == 0)
    {
      start_switch_context(&ret.sanitizer.fake_stack_save, context->sanitizer.bottom, context->sanitizer.size);
      setcontext(&context->uctx);
    }
    return true;
  }

  static void monad_async_context_destroy(struct context *context)
  {
    if (context->stack_storage != nullptr)
    {
#if MONAD_ASYNC_CONTEXT_PRINTING
      printf("*** Execution context %p is destroyed\n", context);
#endif
      munmap(context->stack_storage, context->uctx.uc_stack.ss_size);
      context->stack_storage = nullptr;
    }
  }
#ifdef __cplusplus
}
#endif

#endif

#ifdef __cplusplus
extern "C"
{
#endif

  struct monad_async_task_impl
  {
    struct monad_async_task_head head;
    struct monad_async_task_impl *prev, *next;
    struct context context;
  };

#define LIST_DEFINE_N(name, type) \
  struct                          \
  {                               \
    type *front, *back;           \
    size_t count;                 \
  } name
#define LIST_DEFINE_P(name, type) \
  struct                          \
  {                               \
    type *front, *back;           \
    size_t count;                 \
  } name[monad_async_priority_max]
#ifdef NDEBUG
#define LIST_CHECK(list)
#else
#define LIST_CHECK(list)                                                                       \
  {                                                                                            \
    typeof((list).front) _item_ = (list).front;                                                \
    for (size_t _n_ = 0; _n_ < (list).count; _n_++)                                            \
    {                                                                                          \
      assert((_n_ + 1 == (list).count && _item_->next == nullptr) || _item_->next != nullptr); \
      assert((_n_ == 0 && _item_->prev == nullptr) || _item_->prev != nullptr);                \
      _item_ = _item_->next;                                                                   \
    }                                                                                          \
  }
#endif
#define LIST_PREPEND(list, item, counter)                       \
  if ((list).front == nullptr)                                  \
  {                                                             \
    assert((list).back == nullptr);                             \
    assert((list).count == 0);                                  \
    (item)->prev = (item)->next = nullptr;                      \
    (list).front = (list).back = (item);                        \
    (list).count++;                                             \
    if ((counter) != nullptr)                                   \
      (*counter)++;                                             \
  }                                                             \
  else                                                          \
  {                                                             \
    assert((list).front->prev == nullptr);                      \
    assert((list).count == 1 || (list).front->next != nullptr); \
    (item)->prev = nullptr;                                     \
    (item)->next = (list).front;                                \
    (list).front->prev = (item);                                \
    (list).front = (item);                                      \
    (list).count++;                                             \
    if ((counter) != nullptr)                                   \
      (*counter)++;                                             \
  }                                                             \
  LIST_CHECK(list)
#define LIST_APPEND(list, item, counter)                       \
  if ((list).back == nullptr)                                  \
  {                                                            \
    assert((list).front == nullptr);                           \
    assert((list).count == 0);                                 \
    (item)->prev = (item)->next = nullptr;                     \
    (list).front = (list).back = (item);                       \
    (list).count++;                                            \
    if ((counter) != nullptr)                                  \
      (*counter)++;                                            \
  }                                                            \
  else                                                         \
  {                                                            \
    assert((list).back->next == nullptr);                      \
    assert((list).count == 1 || (list).back->prev != nullptr); \
    (item)->next = nullptr;                                    \
    (item)->prev = (list).back;                                \
    (list).back->next = (item);                                \
    (list).back = (item);                                      \
    (list).count++;                                            \
    if ((counter) != nullptr)                                  \
      (*counter)++;                                            \
  }                                                            \
  LIST_CHECK(list)
#define LIST_REMOVE(list, item, counter)               \
  if ((list).front == (item) && (list).back == (item)) \
  {                                                    \
    assert((list).count == 1);                         \
    (list).front = (list).back = nullptr;              \
    (list).count = 0;                                  \
    (item)->next = (item)->prev = nullptr;             \
    if ((counter) != nullptr)                          \
      (*counter)--;                                    \
  }                                                    \
  else if ((list).front == (item))                     \
  {                                                    \
    assert((item)->prev == nullptr);                   \
    (item)->next->prev = nullptr;                      \
    (list).front = (item)->next;                       \
    (list).count--;                                    \
    (item)->next = (item)->prev = nullptr;             \
    if ((counter) != nullptr)                          \
      (*counter)--;                                    \
  }                                                    \
  else if ((list).back == (item))                      \
  {                                                    \
    assert((item)->next == nullptr);                   \
    (item)->prev->next = nullptr;                      \
    (list).back = (item)->prev;                        \
    (list).count--;                                    \
    (item)->next = (item)->prev = nullptr;             \
    if ((counter) != nullptr)                          \
      (*counter)--;                                    \
  }                                                    \
  else                                                 \
  {                                                    \
    (item)->prev->next = (item)->next;                 \
    (item)->next->prev = (item)->prev;                 \
    (list).count--;                                    \
    (item)->next = (item)->prev = nullptr;             \
    if ((counter) != nullptr)                          \
      (*counter)--;                                    \
  }                                                    \
  LIST_CHECK(list)

#ifdef __cplusplus
}
#endif
