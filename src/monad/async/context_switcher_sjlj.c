// Prevent glibc stack check for longjmp
#undef _FORTIFY_SOURCE
#define _FORTIFY_SOURCE 0
#define _GNU_SOURCE

// #define MONAD_ASYNC_CONTEXT_PRINTING 1

#include "monad/async/context_switcher.h"

#include "monad/async/task.h"

extern void monad_async_executor_task_detach(monad_async_task task);
#include <assert.h>
#include <errno.h>
#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include <threads.h>

#include <sys/mman.h>
#include <sys/resource.h>
#include <ucontext.h>
#include <unistd.h>

#if MONAD_ASYNC_HAVE_ASAN
    #include <sanitizer/asan_interface.h>
#endif
#if MONAD_ASYNC_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif

monad_async_context_switcher_impl const monad_async_context_switcher_sjlj = {
    .create = monad_async_context_switcher_sjlj_create};

MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_sjlj_create(
    monad_async_context *context, monad_async_context_switcher switcher,
    monad_async_task task, const struct monad_async_task_attr *attr);
MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_sjlj_destroy(monad_async_context context);
static inline void monad_async_context_sjlj_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context);
static inline void monad_async_context_sjlj_resume(
    monad_async_context current_context, monad_async_context new_context);
MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_sjlj_resume_many(
    monad_async_context_switcher switcher,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context fake_current_context),
    void *user_ptr);

static inline size_t get_rlimit_stack()
{
    static size_t v;
    if (v != 0) {
        return v;
    }
    struct rlimit r = {0, 0};
    getrlimit(RLIMIT_STACK, &r);
    if (r.rlim_cur == 0 || r.rlim_cur == RLIM_INFINITY) {
        r.rlim_cur = 2 * 1024 * 1024;
    }
    v = (size_t)r.rlim_cur;
    return v;
}

struct monad_async_context_sjlj
{
    struct monad_async_context_head head;
    void *stack_storage;
    ucontext_t uctx;
    jmp_buf buf;
#if MONAD_ASYNC_HAVE_TSAN
    struct
    {
        void *fiber;
    } tsan;
#endif
};

struct monad_async_context_switcher_sjlj
{
    struct monad_async_context_switcher_head head;
    thrd_t owning_thread;
    size_t within_resume_many;
    struct monad_async_context_sjlj *last_suspended;
    struct monad_async_context_sjlj resume_many_context;
};

static inline monad_async_result
monad_async_context_switcher_sjlj_destroy(monad_async_context_switcher switcher)
{
    struct monad_async_context_switcher_sjlj *p =
        (struct monad_async_context_switcher_sjlj *)switcher;
    assert(!p->within_resume_many);
    unsigned contexts =
        atomic_load_explicit(&p->head.contexts, memory_order_acquire);
    if (contexts != 0) {
        fprintf(
            stderr,
            "FATAL: Context switcher destroyed whilst %u contexts still using "
            "it.\n",
            contexts);
        abort();
    }
    free(p);
    return monad_async_make_success(0);
}

monad_async_result
monad_async_context_switcher_sjlj_create(monad_async_context_switcher *switcher)
{
    struct monad_async_context_switcher_sjlj *p =
        (struct monad_async_context_switcher_sjlj *)calloc(
            1, sizeof(struct monad_async_context_switcher_sjlj));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    static const struct monad_async_context_switcher_head to_copy = {
        .contexts = 0,
        .self_destroy = monad_async_context_switcher_sjlj_destroy,
        .create = monad_async_context_sjlj_create,
        .destroy = monad_async_context_sjlj_destroy,
        .suspend_and_call_resume =
            monad_async_context_sjlj_suspend_and_call_resume,
        .resume = monad_async_context_sjlj_resume,
        .resume_many = monad_async_context_sjlj_resume_many};
    memcpy(&p->head, &to_copy, sizeof(to_copy));
    p->owning_thread = thrd_current();
    atomic_store_explicit(
        &p->resume_many_context.head.switcher, &p->head, memory_order_release);
#if MONAD_ASYNC_HAVE_TSAN
    p->resume_many_context.tsan.fiber = __tsan_get_current_fiber();
#endif
    *switcher = (monad_async_context_switcher)p;
    return monad_async_make_success(0);
}

/*****************************************************************************/
#if MONAD_ASYNC_HAVE_ASAN || MONAD_ASYNC_HAVE_TSAN
static inline __attribute__((always_inline)) void start_switch_context(
    struct monad_async_context_sjlj *dest_context, void **fake_stack_save,
    void const *bottom, size_t size)
{
    (void)dest_context;
    (void)fake_stack_save;
    (void)bottom;
    (void)size;
    #if MONAD_ASYNC_HAVE_ASAN
    __sanitizer_start_switch_fiber(fake_stack_save, bottom, size);
    #endif
    #if MONAD_ASYNC_HAVE_TSAN
    __tsan_switch_to_fiber(dest_context->tsan.fiber, 0);
    #endif
}

static inline __attribute__((always_inline)) void finish_switch_context(
    struct monad_async_context_sjlj *dest_context, void *fake_stack_save,
    void const **bottom_old, size_t *size_old)
{
    (void)dest_context;
    (void)fake_stack_save;
    (void)bottom_old;
    (void)size_old;
    #if MONAD_ASYNC_HAVE_ASAN
    __sanitizer_finish_switch_fiber(fake_stack_save, bottom_old, size_old);
    #endif
}
#else
static inline void start_switch_context(
    struct monad_async_context_sjlj *, void **, void const *, size_t)
{
}

static inline void finish_switch_context(
    struct monad_async_context_sjlj *, void *, void const **, size_t *)
{
}
#endif

static void monad_async_context_sjlj_task_runner(
    struct monad_async_context_sjlj *context, monad_async_task task)
{
    // We are now at the base of our custom stack
    //
    // WARNING: This custom stack will get freed without unwind
    // This is why when not in use, it sits at the setjmp in this base runner
    // function
    //
    // TODO: We currently don't tell the sanitiser to free its resources
    // associated with this context upon deallocation. For this, we need to
    // call:
    //
    // start_switch_context(nullptr, ret->sanitizer.bottom,
    // ret->sanitizer.size);
    //
    // just before the final longjmp out.

#if MONAD_ASYNC_HAVE_ASAN
    // First time call fake_stack_save will be null which means no historical
    // stack to restore for this brand new context
    assert(context->head.sanitizer.fake_stack_save == nullptr);
#endif
    finish_switch_context(
        context,
        context->head.sanitizer.fake_stack_save,
        &context->head.sanitizer.bottom,
        &context->head.sanitizer.size);
#if MONAD_ASYNC_CONTEXT_PRINTING
    printf(
        "*** %d: New execution context %p launches\n",
        gettid(),
        (void *)context);
    fflush(stdout);
#endif
    size_t const page_size = (size_t)getpagesize();
    void *stack_base = (void *)((uintptr_t)context->stack_storage +
                                context->uctx.uc_stack.ss_size + page_size);
    void *stack_front = (void *)((uintptr_t)context->stack_storage + page_size);
    (void)stack_base;
    (void)stack_front;
    for (;;) {
        // Tell the Linux kernel that this stack can be lazy reclaimed if there
        // is memory pressure
        madvise(
            stack_front, context->uctx.uc_stack.ss_size - page_size, MADV_FREE);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p suspends in base task runner "
            "awaiting code to run\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
        monad_async_context_sjlj_suspend_and_call_resume(
            &context->head, nullptr);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p resumes in base task runner, begins "
            "executing task.\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
#ifndef NDEBUG
        struct monad_async_context_switcher_sjlj *switcher =
            (struct monad_async_context_switcher_sjlj *)atomic_load_explicit(
                &context->head.switcher, memory_order_acquire);
        if (switcher->owning_thread != thrd_current()) {
            fprintf(
                stderr,
                "FATAL: Context being switched on a kernel thread different to "
                "the assigned context switcher.\n");
            abort();
        }
#endif
        // Execute the task
        task->result = task->user_code(task);
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p returns to base task runner, task "
            "has "
            "exited\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
        monad_async_executor_task_detach(task);
    }
}

static monad_async_result monad_async_context_sjlj_create(
    monad_async_context *context, monad_async_context_switcher switcher_,
    monad_async_task task, const struct monad_async_task_attr *attr)
{
    struct monad_async_context_switcher_sjlj *switcher =
        (struct monad_async_context_switcher_sjlj *)switcher_;
    struct monad_async_context_sjlj *p =
        (struct monad_async_context_sjlj *)calloc(
            1, sizeof(struct monad_async_context_sjlj));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    atomic_store_explicit(&p->head.switcher, switcher_, memory_order_release);
    size_t stack_size = attr->stack_size;
    if (stack_size == 0) {
        stack_size = get_rlimit_stack();
    }
    size_t const page_size = (size_t)getpagesize();
    p->stack_storage = mmap(
        nullptr,
        stack_size + page_size,
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS,
        -1,
        0);
    if (p->stack_storage == MAP_FAILED) {
        p->stack_storage = nullptr;
        return monad_async_make_failure(errno);
    }
    void *stack_base =
        (void *)((uintptr_t)p->stack_storage + stack_size + page_size);
    void *stack_front = (void *)((uintptr_t)p->stack_storage + page_size);
    // Put guard page at the front
    mmap(
        p->stack_storage,
        page_size,
        PROT_NONE,
        MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED | MAP_NORESERVE,
        -1,
        0);
#if MONAD_ASYNC_CONTEXT_PRINTING
    printf(
        "*** %d: New execution context %p is given stack between %p-%p with "
        "guard "
        "page at %p\n",
        gettid(),
        (void *)p,
        (void *)stack_front,
        (void *)stack_base,
        (void *)p->stack_storage);
    fflush(stdout);
#endif
    // Clone the current execution context
    if (getcontext(&p->uctx) == -1) {
        monad_async_result ret = monad_async_make_failure(errno);
        (void)monad_async_context_sjlj_destroy(&p->head);
        return ret;
    }
    // Replace its stack
    p->uctx.uc_stack.ss_size = stack_size;
    p->uctx.uc_stack.ss_sp = stack_front;
    p->head.sanitizer.bottom = stack_base;
    p->head.sanitizer.size = stack_size;
    // Launch execution, suspending immediately
    makecontext(
        &p->uctx,
        (void (*)(void))monad_async_context_sjlj_task_runner,
        2,
        p,
        task);
#if MONAD_ASYNC_HAVE_TSAN
    p->tsan.fiber = __tsan_create_fiber(0);
#endif
    if (setjmp(switcher->resume_many_context.buf) == 0) {
        switcher->within_resume_many = true;
        start_switch_context(
            p,
            &switcher->resume_many_context.head.sanitizer.fake_stack_save,
            p->head.sanitizer.bottom,
            p->head.sanitizer.size);
        setcontext(&p->uctx);
    }
    finish_switch_context(
        &switcher->resume_many_context,
        switcher->resume_many_context.head.sanitizer.fake_stack_save,
        nullptr,
        nullptr);
    switcher->within_resume_many = false;
    atomic_fetch_add_explicit(&switcher_->contexts, 1, memory_order_relaxed);
    *context = (monad_async_context)p;
    return monad_async_make_success(0);
}

static monad_async_result
monad_async_context_sjlj_destroy(monad_async_context context)
{
    struct monad_async_context_sjlj *p =
        (struct monad_async_context_sjlj *)context;
#if MONAD_ASYNC_HAVE_TSAN
    if (p->tsan.fiber != nullptr) {
        __tsan_destroy_fiber(p->tsan.fiber);
        p->tsan.fiber = nullptr;
    }
#endif
    if (p->stack_storage != nullptr) {
#if MONAD_ASYNC_CONTEXT_PRINTING
        printf(
            "*** %d: Execution context %p is destroyed\n",
            gettid(),
            (void *)context);
        fflush(stdout);
#endif
        size_t const page_size = (size_t)getpagesize();
        if (munmap(p->stack_storage, p->uctx.uc_stack.ss_size + page_size) ==
            -1) {
            return monad_async_make_failure(errno);
        }
        p->stack_storage = nullptr;
    }
    atomic_fetch_sub_explicit(
        &atomic_load_explicit(&context->switcher, memory_order_acquire)
             ->contexts,
        1,
        memory_order_relaxed);
    free(context);
    return monad_async_make_success(0);
}

static void monad_async_context_sjlj_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context)
{
    struct monad_async_context_sjlj *p =
        (struct monad_async_context_sjlj *)current_context;
    int ret = setjmp(p->buf);
    if (ret != 0) {
        // He has resumed
        finish_switch_context(
            (struct monad_async_context_sjlj *)new_context,
            p->head.sanitizer.fake_stack_save,
            &p->head.sanitizer.bottom,
            &p->head.sanitizer.size);
        assert((int)((uintptr_t)p ^ ((uintptr_t)p >> 32)) == ret);
        return;
    }
    // Set last suspended
    struct monad_async_context_switcher_sjlj *switcher =
        (struct monad_async_context_switcher_sjlj *)atomic_load_explicit(
            &p->head.switcher, memory_order_acquire);
    switcher->last_suspended = p;
    if (new_context != nullptr) {
        // Call resume on the destination switcher
        atomic_load_explicit(&new_context->switcher, memory_order_acquire)
            ->resume(current_context, new_context);
        // Some switchers return, and that's okay
    }
    else {
        // Return to base
        monad_async_context_sjlj_resume(
            current_context, &switcher->resume_many_context.head);
    }
}

static void monad_async_context_sjlj_resume(
    monad_async_context current_context, monad_async_context new_context)
{
#if MONAD_ASYNC_CONTEXT_PRINTING
    {
        struct monad_async_context_switcher_sjlj *switcher =
            (struct monad_async_context_switcher_sjlj *)atomic_load_explicit(
                &new_context->switcher, memory_order_acquire);
        bool new_context_is_resume_all_context =
            (new_context == &switcher->resume_many_context.head);
        printf(
            "*** %d: Execution context %p initiates resumption of execution in "
            "context "
            "%p (is_resume_many_context = %d)\n",
            gettid(),
            (void *)current_context,
            (void *)new_context,
            new_context_is_resume_all_context);
        fflush(stdout);
    }
#endif
    struct monad_async_context_sjlj *p =
        (struct monad_async_context_sjlj *)new_context;
    start_switch_context(
        p,
        &current_context->sanitizer.fake_stack_save,
        new_context->sanitizer.bottom,
        new_context->sanitizer.size);
    longjmp(p->buf, (int)((uintptr_t)p ^ ((uintptr_t)p >> 32)));
}

static monad_async_result monad_async_context_sjlj_resume_many(
    monad_async_context_switcher switcher_,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context just_suspended),
    void *user_ptr)
{
    struct monad_async_context_switcher_sjlj *switcher =
        (struct monad_async_context_switcher_sjlj *)switcher_;
    switcher->last_suspended = nullptr;
    jmp_buf old_buf;
    if (switcher->within_resume_many++ > 0) {
        memcpy(&old_buf, &switcher->resume_many_context.buf, sizeof(old_buf));
    }
    int ret = setjmp(switcher->resume_many_context.buf);
    if (ret != 0) {
        // He has resumed
        finish_switch_context(
            &switcher->resume_many_context,
            switcher->resume_many_context.head.sanitizer.fake_stack_save,
            &switcher->resume_many_context.head.sanitizer.bottom,
            &switcher->resume_many_context.head.sanitizer.size);
        assert(
            (int)((uintptr_t)&switcher->resume_many_context ^
                  ((uintptr_t)&switcher->resume_many_context >> 32)) == ret);
    }
    monad_async_result r =
        resumed(user_ptr, &switcher->resume_many_context.head);
    if (switcher->within_resume_many-- > 0) {
        memcpy(&switcher->resume_many_context.buf, &old_buf, sizeof(old_buf));
    }
    return r;
}
