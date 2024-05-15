#include <monad/fiber/assert.h>
#include <monad/fiber/current.h>
#include <threads.h>
#include <unistd.h>

#if defined(MONAD_USE_TSAN)
    #include <sanitizer/tsan_interface.h>
#endif

extern thread_local monad_fiber_context_t monad_fiber_main_fiber_context_;
extern thread_local monad_fiber_t monad_fiber_main_fiber_;

extern int pthread_getname_np(pthread_t thread, char *name, size_t size);

monad_fiber_t *monad_fiber_main()
{
    MONAD_DEBUG_ASSERT(monad_fiber_main_fiber_.context != NULL);
    return &monad_fiber_main_fiber_;
}

extern thread_local monad_fiber_t *monad_fiber_current_;

void monad_fiber_init_main()
{
    if (monad_fiber_main_fiber_.context == NULL) {

        char buffer[256];
        if (0 == pthread_getname_np(pthread_self(), buffer, 256ull)) {
            monad_fiber_set_name(&monad_fiber_main_fiber_context_, buffer);
        }
        monad_fiber_main_fiber_.context = &monad_fiber_main_fiber_context_;
        MONAD_DEBUG_ASSERT(monad_fiber_main_fiber_.context->fiber == NULL);
#if defined(MONAD_USE_TSAN)
        monad_fiber_main_fiber_.context->tsan_fiber =
            __tsan_get_current_fiber();
#endif
    }

    MONAD_DEBUG_ASSERT(
        monad_fiber_current_ == NULL ||
        monad_fiber_current_ == &monad_fiber_main_fiber_);
    monad_fiber_current_ = &monad_fiber_main_fiber_;
}

extern thread_local monad_fiber_t *monad_fiber_current_;

monad_fiber_t *monad_fiber_current()
{
    MONAD_DEBUG_ASSERT(monad_fiber_current_ != NULL);
    return monad_fiber_current_;
}

monad_fiber_t *monad_fiber_activate_fiber(monad_fiber_t *new_current)
{
    monad_fiber_t *pre = monad_fiber_current();
    monad_fiber_current_ = new_current;
    return pre;
}

void monad_fiber_switch_to_fiber(monad_fiber_t *target)
{
    MONAD_DEBUG_ASSERT(target != NULL);
    monad_fiber_t *pre = monad_fiber_current();
    monad_fiber_current_ = target;

    // LOG here
    (void)monad_fiber_context_switch(pre->context, target->context);
    MONAD_ASSERT(
        monad_fiber_current_ == pre); // make sure we switched back through
    // monad_fiber_switch_current_fiber
}

void monad_fiber_switch_to_main()
{
    // LOG here
    monad_fiber_switch_to_fiber(monad_fiber_main());
}

static monad_fiber_context_t *
monad_fiber_yield_impl(monad_fiber_context_t *, void *arg_)
{
    monad_fiber_task_t *task = (monad_fiber_task_t *)arg_;
    monad_fiber_t *ctx = monad_fiber_main();
    monad_fiber_activate_fiber(ctx);
    task->resume(task);
    return ctx->context;
}

void monad_fiber_yield()
{
    // check
    monad_fiber_t *cc = monad_fiber_current();
    MONAD_ASSERT(cc->scheduler != NULL);
    monad_fiber_task_t *t = monad_fiber_scheduler_pop_higher_priority_task(
        cc->scheduler, cc->priority);
    if (t == NULL) {
        return; // not work, no problem
    }

    monad_fiber_context_switch_with(
        cc->context, monad_fiber_main_context(), &monad_fiber_yield_impl, &t);

    monad_fiber_activate_fiber(cc);
}

struct monad_fiber_await_impl_t
{
    monad_fiber_t *fiber;
    void (*suspend_to)(monad_fiber_t * /*task */, void * /*arg*/);
    void *arg;
};

static monad_fiber_context_t *
monad_fiber_await_impl(monad_fiber_context_t *from, void *ptr)
{
    struct monad_fiber_await_impl_t impl =
        *(struct monad_fiber_await_impl_t *)ptr;
    (*impl.suspend_to)(impl.fiber, impl.arg);
    return from;
}

void monad_fiber_await(
    void (*suspend_to)(monad_fiber_t * /*task */, void * /*arg*/), void *arg)
{
    monad_fiber_t *from = monad_fiber_current();
    // Mustn't be called from main context!
    if (from->context != monad_fiber_main_context()) {
        MONAD_ASSERT(from->scheduler != NULL);

        if (!monad_fiber_run_one(from->scheduler)) {
            usleep(1000);
        }

        return;
    }

    struct monad_fiber_await_impl_t impl = {
        .fiber = from, .suspend_to = suspend_to, .arg = arg};

    monad_fiber_context_switch_with(
        from->context,
        monad_fiber_main_context(),
        &monad_fiber_await_impl,
        &impl);
}
