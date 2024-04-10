#include "monad/async/context_switcher.h"

#include "monad/async/executor.h"

#include "task_impl.h"

#include <errno.h>
#include <stdio.h>
#include <threads.h>

MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_none_create(
    monad_async_context *context, monad_async_context_switcher switcher,
    monad_async_task task, const struct monad_async_task_attr *attr);
MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_none_destroy(monad_async_context context);
static inline void monad_async_context_none_launch_new_work(
    monad_async_context context, monad_async_task task);
static inline void monad_async_context_none_suspend_and_call_resume(
    monad_async_context current_context, monad_async_context new_context);
static inline void monad_async_context_none_resume(
    monad_async_context current_context, monad_async_context new_context);
MONAD_ASYNC_NODISCARD static inline monad_async_result
monad_async_context_none_resume_many(
    monad_async_context_switcher switcher,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context just_suspended),
    void *user_ptr);

static inline monad_async_result
monad_async_context_switcher_none_destroy(monad_async_context_switcher switcher)
{
    return monad_async_make_success(0);
}

struct monad_async_context_none
{
    struct monad_async_context_head head;
    monad_async_task task;
};

static struct monad_async_context_switcher_none
{
    struct monad_async_context_switcher_head head;
} context_switcher_none_instance = {
    {.contexts = 0,
     .self_destroy = monad_async_context_switcher_none_destroy,
     .create = monad_async_context_none_create,
     .destroy = monad_async_context_none_destroy,
     .suspend_and_call_resume =
         monad_async_context_none_suspend_and_call_resume,
     .resume = monad_async_context_none_resume,
     .resume_many = monad_async_context_none_resume_many}};

static thread_local size_t context_switcher_none_instance_within_resume_many;

monad_async_result
monad_async_context_switcher_none_create(monad_async_context_switcher *switcher)
{
    *switcher = &context_switcher_none_instance.head;
    return monad_async_make_success(0);
}

/*****************************************************************************/

static monad_async_result monad_async_context_none_create(
    monad_async_context *context, monad_async_context_switcher switcher_,
    monad_async_task task, const struct monad_async_task_attr *attr)
{
    struct monad_async_context_none *p =
        (struct monad_async_context_none *)calloc(
            1, sizeof(struct monad_async_context_none));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    p->task = task;
    p->head.switcher = switcher_;
    switcher_->contexts++;
    *context = (monad_async_context)p;
    return monad_async_make_success(0);
}

static monad_async_result
monad_async_context_none_destroy(monad_async_context context)
{
    context->switcher->contexts--;
    free(context);
    return monad_async_make_success(0);
}

static void monad_async_context_none_suspend_and_call_resume(
    monad_async_context, monad_async_context)
{
    fprintf(
        stderr,
        "FATAL: The none context switcher cannot suspend tasks, and therefore "
        "cannot resume them.\n");
    abort();
}

static void monad_async_context_none_resume(
    monad_async_context, monad_async_context new_context)
{
    if (context_switcher_none_instance_within_resume_many == 0) {
        fprintf(
            stderr,
            "FATAL: The none context switcher cannot suspend tasks, and "
            "therefore cannot resume them.\n");
        abort();
    }
    struct monad_async_context_none *p =
        (struct monad_async_context_none *)new_context;
    // Execute the task
    p->task->result = p->task->user_code(p->task);
    monad_async_executor_task_exited(p->task);
}

static monad_async_result monad_async_context_none_resume_many(
    monad_async_context_switcher,
    monad_async_result (*resumed)(
        void *user_ptr, monad_async_context just_suspended),
    void *user_ptr)
{
    context_switcher_none_instance_within_resume_many++;
    monad_async_result r = resumed(user_ptr, nullptr);
    context_switcher_none_instance_within_resume_many--;
    return r;
}
