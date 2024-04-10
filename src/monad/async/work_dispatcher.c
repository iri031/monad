#include "monad/async/work_dispatcher.h"

#include <errno.h>
#include <stdlib.h>

struct monad_async_work_dispatcher_impl
{
    struct monad_async_work_dispatcher_head head;
};

struct monad_async_work_dispatcher_executor_impl
{
    struct monad_async_work_dispatcher_executor_head head;
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
    (void)attr;
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
    monad_async_work_dispatcher_executor *ex, monad_async_work_dispatcher dp,
    struct monad_async_work_dispatcher_executor_attr *attr)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)calloc(
            1, sizeof(struct monad_async_work_dispatcher_executor_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    (void)dp;
    (void)attr;
    *ex = (monad_async_work_dispatcher_executor)p;
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_executor_destroy(
    monad_async_work_dispatcher_executor ex)
{
    struct monad_async_work_dispatcher_executor_impl *p =
        (struct monad_async_work_dispatcher_executor_impl *)ex;
    free(p);
    return monad_async_make_success(0);
}

monad_async_result monad_async_work_dispatcher_executor_run(
    monad_async_work_dispatcher_executor ex)
{
    (void)ex;
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
    (void)max_undispatched;
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
