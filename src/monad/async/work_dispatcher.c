#include "monad/async/work_dispatcher.h"

#include "executor_impl.h"

#include <errno.h>
#include <stdlib.h>
#include <threads.h>

struct monad_async_work_dispatcher_executor_impl
{
    struct monad_async_work_dispatcher_executor_head head;
    struct monad_async_executor_impl derived;
    struct monad_async_work_dispatcher_executor_impl *prev, *next;
};

struct monad_async_work_dispatcher_impl
{
    struct monad_async_work_dispatcher_head head;
    uint32_t spin_before_sleep_ms;

    // all items below this require taking the lock
    atomic_int lock;

    struct
    {
        LIST_DEFINE_N(
            working, struct monad_async_work_dispatcher_executor_impl);
        LIST_DEFINE_N(idle, struct monad_async_work_dispatcher_executor_impl);
    } executors;

    LIST_DEFINE_P(tasks_awaiting_dispatch, struct monad_async_task_impl);
};

monad_async_result monad_async_work_dispatcher_create(
    monad_async_work_dispatcher *dp,
    struct monad_async_work_dispatcher_attr *attr)
{
    struct monad_async_work_dispatcher_impl *p =
        (struct monad_async_work_dispatcher_impl *)calloc(
            1, sizeof(struct monad_async_work_dispatcher_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    p->spin_before_sleep_ms = attr->spin_before_sleep_ms;
    *dp = (monad_async_work_dispatcher)p;
    return monad_async_make_success(0);
}

monad_async_result
monad_async_work_dispatcher_destroy(monad_async_work_dispatcher dp)
{
    struct monad_async_work_dispatcher_impl *p =
        (struct monad_async_work_dispatcher_impl *)dp;
    free(p);
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_executor_create(
    monad_async_work_dispatcher_executor *ex, monad_async_work_dispatcher dp_,
    struct monad_async_work_dispatcher_executor_attr *attr)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)calloc(
            1, sizeof(struct monad_async_work_dispatcher_executor_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    MONAD_ASYNC_TRY_RESULT(
        (void)monad_async_work_dispatcher_executor_destroy(
            (monad_async_work_dispatcher_executor)p),
        monad_async_executor_create_impl(&p->derived, &attr->derived));
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)dp_;
    struct monad_async_work_dispatcher_executor_head head = {
        .derived = &p->derived.head,
        .dispatcher = dp_,
        .is_idle = true,
        .is_working = false};
    memcpy(&p->head, &head, sizeof(head));
    LIST_APPEND_ATOMIC_COUNTER(dp->executors.idle, p, &dp_->executors.idle);
    *ex = (monad_async_work_dispatcher_executor)p;
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_executor_destroy(
    monad_async_work_dispatcher_executor ex)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)ex;
    MONAD_ASYNC_TRY_RESULT(, monad_async_executor_destroy_impl(&p->derived));
    struct monad_async_work_dispatcher_impl *dp =
        (struct monad_async_work_dispatcher_impl *)p->head.dispatcher;
    if (p->head.is_idle) {
        LIST_REMOVE_ATOMIC_COUNTER(
            dp->executors.idle, p, &dp->head.executors.idle);
    }
    if (p->head.is_working) {
        LIST_REMOVE_ATOMIC_COUNTER(
            dp->executors.working, p, &dp->head.executors.working);
    }
    free(p);
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_executor_run(
    monad_async_work_dispatcher_executor ex)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)ex;
    struct timespec ts = {0, 1000000}; // 1 millisecond
    monad_async_result r = monad_async_executor_run(&p->derived.head, 256, &ts);
    MONAD_ASYNC_TRY_RESULT(, r);
    // todo
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_submit(
    monad_async_work_dispatcher dp, monad_async_task *tasks, size_t count)
{
    (void)dp;
    (void)tasks;
    (void)count;
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_wait(
    monad_async_work_dispatcher dp, size_t max_undispatched,
    size_t max_unexecuted, struct timespec *timeout)
{
    (void)dp;
    (void)max_undispatched;
    (void)max_unexecuted;
    (void)timeout;
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_quit(
    monad_async_work_dispatcher dp, size_t count, struct timespec *timeout)
{
    (void)dp;
    (void)count;
    (void)timeout;
    return monad_async_make_success(0);
}
