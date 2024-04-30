#include "monad/async/file_io.h"

#include "monad/async/executor.h"

// #define MONAD_ASYNC_FILE_IO_PRINTING 1

#include "executor_impl.h"
#include "task_impl.h"

#include <errno.h>

#include <fcntl.h>

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
    p->io_uring_file_index = (unsigned)-1;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    unsigned file_index = monad_async_executor_alloc_file_index(ex, &p->head);
    if (file_index == (unsigned)-1) {
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return monad_async_make_failure(ENOMEM);
    }
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_openat2_direct(
        sqe,
        (base == nullptr)
            ? AT_FDCWD
            : (int)((struct monad_async_file_impl *)base)->io_uring_file_index,
        subpath,
        how,
        file_index);
    io_uring_sqe_set_data(sqe, task, task);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_open\n",
        (void *)task,
        (void *)ex);
#endif
    monad_async_result ret = monad_async_executor_suspend_impl(
        ex, task, monad_async_task_file_create_cancel, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "file_open with file_index=%u\n",
        (void *)task,
        (void *)ex,
        file_index);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        monad_async_executor_free_file_index(ex, file_index, &p->head);
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return ret;
    }
    p->io_uring_file_index = file_index;
    *file = (monad_async_file)p;
    return monad_async_make_success(0);
}

monad_async_result
monad_async_task_file_destroy(monad_async_task task_, monad_async_file file_)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    if (file->io_uring_file_index != (unsigned)-1) {
        struct monad_async_task_impl *task =
            (struct monad_async_task_impl *)task_;
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)atomic_load_explicit(
                &task_->current_executor, memory_order_acquire);
        struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
        io_uring_prep_close(sqe, 0);
        __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index);
        io_uring_sqe_set_data(sqe, task, task);

#if MONAD_ASYNC_FILE_IO_PRINTING
        printf(
            "*** Task %p running on executor %p initiates "
            "file_close\n",
            (void *)task,
            (void *)ex);
#endif
        monad_async_result ret =
            monad_async_executor_suspend_impl(ex, task, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
        printf(
            "*** Task %p running on executor %p completes "
            "file_close for file_index=%u\n",
            (void *)task,
            (void *)ex,
            file->io_uring_file_index);
#endif
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
            return ret;
        }
        monad_async_executor_free_file_index(
            ex, file->io_uring_file_index, &file->head);
    }
    free(file);
    return monad_async_make_success(0);
}

monad_async_result monad_async_task_file_fallocate(
    monad_async_task task_, monad_async_file file_, int mode,
    monad_async_file_offset offset, monad_async_file_offset len)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task);
    io_uring_prep_fallocate(
        sqe, (int)file->io_uring_file_index, mode, (off_t)offset, (off_t)len);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, task, task);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_allocate\n",
        (void *)task,
        (void *)ex);
#endif
    monad_async_result ret =
        monad_async_executor_suspend_impl(ex, task, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "file_allocate for file_index=%u\n",
        (void *)task,
        (void *)ex,
        file->io_uring_file_index);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        return ret;
    }
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
    monad_async_file file_, int buffer_index, const struct iovec *iovecs,
    unsigned nr_vecs, monad_async_file_offset offset, int flags)
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
    if (buffer_index == 0) {
        if (nr_vecs != 1) {
            (void)flags;
            io_uring_prep_readv(
                sqe, (int)file->io_uring_file_index, iovecs, nr_vecs, offset);
        }
        else {
            io_uring_prep_read(
                sqe,
                (int)file->io_uring_file_index,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset);
        }
    }
    else {
        assert(buffer_index > 0);
        if (nr_vecs != 1) {
            assert(false);
            abort();
        }
        else {
            io_uring_prep_read_fixed(
                sqe,
                (int)file->io_uring_file_index,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset,
                buffer_index - 1);
        }
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_read on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_write(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, int buffer_index, const struct iovec *iovecs,
    unsigned nr_vecs, monad_async_file_offset offset, int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_wrsqe_suspending_if_necessary(ex, task);
#ifdef IO_URING_VERSION_MAJOR
    #error "Implement io_uring_prep_writev2 support"
#endif
    if (buffer_index == 0) {
        if (nr_vecs != 1) {
            (void)flags;
            io_uring_prep_writev(
                sqe, (int)file->io_uring_file_index, iovecs, nr_vecs, offset);
        }
        else {
            io_uring_prep_write(
                sqe,
                (int)file->io_uring_file_index,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset);
        }
    }
    else {
        assert(buffer_index < 0);
        if (nr_vecs != 1) {
            assert(false);
            abort();
        }
        else {
            io_uring_prep_write_fixed(
                sqe,
                (int)file->io_uring_file_index,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset,
                -1 - buffer_index);
        }
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_write on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
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
    io_uring_prep_sync_file_range(
        sqe, (int)file->io_uring_file_index, bytes, offset, flags);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "range_sync on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
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
    io_uring_prep_fsync(sqe, (int)file->io_uring_file_index, 0);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task);
    iostatus->cancel_ = monad_async_task_file_io_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "durable_sync on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}
