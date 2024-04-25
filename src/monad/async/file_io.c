#include "monad/async/file_io.h"

#include "monad/async/executor.h"

#include "executor_impl.h"
#include "task_impl.h"

#include <errno.h>

#include <fcntl.h>

#ifndef IORING_FILE_INDEX_ALLOC
    #define IORING_FILE_INDEX_ALLOC (~0U)
#endif

struct monad_async_file_impl
{
    struct monad_async_file_head head;
    unsigned io_uring_file_index; // NOT a traditional file descriptor!
};

static inline monad_async_result
monad_async_task_file_create_cancel(struct monad_async_task_impl *task)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(task), 0);
    return monad_async_make_success(EAGAIN); // Canceller needs to wait
}

monad_async_result monad_async_task_file_create(
    monad_async_file *file, monad_async_task task_, monad_async_file base,
    char const *subpath, struct open_how *how)
{
    struct monad_async_file_impl *p = (struct monad_async_file_impl *)calloc(
        1, sizeof(struct monad_async_file_impl));
    if (p == nullptr) {
        return monad_async_make_failure(errno);
    }
    p->head.executor = task_->current_executor;
    p->io_uring_file_index = IORING_FILE_INDEX_ALLOC;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_openat2_direct(
        sqe,
        (base == nullptr)
            ? AT_FDCWD
            : (int)((struct monad_async_file_impl *)base)->io_uring_file_index,
        subpath,
        how,
        IORING_FILE_INDEX_ALLOC);
    io_uring_sqe_set_data(sqe, task, task);

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_open\n",
        task,
        ex);
#endif
    monad_async_result ret = monad_async_executor_suspend_impl(
        ex, task, monad_async_task_file_create_cancel, nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "file_open\n",
        task,
        ex);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return ret;
    }
    p->io_uring_file_index = (unsigned)ret.value;
    *file = (monad_async_file)p;
    return monad_async_make_success(0);
}

monad_async_result
monad_async_task_file_destroy(monad_async_task task_, monad_async_file file_)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    if (file->io_uring_file_index != IORING_FILE_INDEX_ALLOC) {
        struct monad_async_task_impl *task =
            (struct monad_async_task_impl *)task_;
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)atomic_load_explicit(
                &task_->current_executor, memory_order_acquire);
        struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
        io_uring_prep_close(sqe, 0);
        __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index);
        io_uring_sqe_set_data(sqe, task, task);

#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Task %p running on executor %p initiates "
            "file_close\n",
            task,
            ex);
#endif
        monad_async_result ret =
            monad_async_executor_suspend_impl(ex, task, nullptr, nullptr);
#if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Task %p running on executor %p completes "
            "file_close\n",
            task,
            ex);
#endif
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
            return ret;
        }
    }
    free(file);
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_task_file_io_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(iostatus), 0);
    return monad_async_make_success(EAGAIN); // Canceller needs to wait
}

void monad_async_task_file_read(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, const struct iovec *iovecs, unsigned nr_vecs,
    monad_async_file_offset offset, int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
#ifdef IO_URING_VERSION_MAJOR
    #error "Implement io_uring_prep_readv2 support"
#endif
    if (nr_vecs != 1) {
        (void)flags;
        io_uring_prep_readv(sqe, 0, iovecs, nr_vecs, offset);
    }
    else {
        io_uring_prep_read(
            sqe, 0, iovecs[0].iov_base, (unsigned)iovecs[0].iov_len, offset);
    }
    __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index);
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_read\n",
        task,
        ex);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_write(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, const struct iovec *iovecs, unsigned nr_vecs,
    monad_async_file_offset offset, int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
#ifdef IO_URING_VERSION_MAJOR
    #error "Implement io_uring_prep_writev2 support"
#endif
    if (nr_vecs != 1) {
        (void)flags;
        io_uring_prep_writev(sqe, 0, iovecs, nr_vecs, offset);
    }
    else {
        io_uring_prep_write(
            sqe, 0, iovecs[0].iov_base, (unsigned)iovecs[0].iov_len, offset);
    }
    __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index);
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_write\n",
        task,
        ex);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_range_sync(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, unsigned bytes, monad_async_file_offset offset,
    int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_sync_file_range(sqe, 0, bytes, offset, flags);
    __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index);
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "range_sync\n",
        task,
        ex);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_durable_sync(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_fsync(sqe, 0, 0);
    __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index);
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;

#if MONAD_ASYNC_EXECUTOR_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "durable_sync\n",
        task,
        ex);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}
