#pragma once

#include "task_impl.h"

#include <assert.h>
#include <stdio.h>
#include <threads.h>

#include <execinfo.h>
#include <linux/ioprio.h>
#include <poll.h>
#include <sys/eventfd.h>
#include <sys/mman.h>
#include <unistd.h>

#if MONAD_ASYNC_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif

typedef struct monad_async_file_head *monad_async_file;

struct monad_async_executor_free_registered_buffer
{
    struct monad_async_executor_free_registered_buffer *next;
    unsigned index;
};

struct monad_async_executor_impl
{
    struct monad_async_executor_head head;

    thrd_t owning_thread;
    bool within_run;
    atomic_bool need_to_empty_eventfd;
    monad_async_context run_context;
    struct io_uring ring, wr_ring;
    unsigned wr_ring_ops_outstanding;
    LIST_DEFINE_P(tasks_running, struct monad_async_task_impl);
    LIST_DEFINE_P(tasks_suspended_awaiting, struct monad_async_task_impl);
    LIST_DEFINE_P(tasks_suspended_completed, struct monad_async_task_impl);
    LIST_DEFINE_N(tasks_exited, struct monad_async_task_impl);
    monad_async_result *_Atomic cause_run_to_return;

    monad_async_file *file_indices;
    unsigned file_indices_size;

    struct monad_async_executor_impl_registered_buffers_t
    {
        struct iovec *buffers;
        unsigned size;
        struct monad_async_executor_free_registered_buffer *free[2];
    } registered_buffers[2];

    // all items below this require taking the lock
    atomic_int lock;
    int eventfd;
    monad_async_priority tasks_pending_launch_next_queue;
    // Note NOT sorted by task priority!
    LIST_DEFINE_P(tasks_pending_launch, struct monad_async_task_impl);
    monad_async_result cause_run_to_return_value;
};

extern monad_async_result monad_async_executor_suspend_impl(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    monad_async_result (*please_cancel)(struct monad_async_task_impl *task),
    monad_async_io_status **completed);

// diseased dead beef in hex, last bit set so won't be a pointer
static uintptr_t const EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC =
    (uintptr_t)0xd15ea5eddeadbeef;

// Cannot exceed three bits
enum io_uring_user_data_type : uint8_t
{
    io_uring_user_data_type_none = 0, // to detect misconfig
    io_uring_user_data_type_task = 1, // payload is a task ptr
    io_uring_user_data_type_iostatus = 2, // payload is an i/o status ptr
    io_uring_user_data_type_magic =
        7 // special values e.g. EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC
};

#define io_uring_mangle_into_data(value)                                        \
    _Generic(                                                                   \
        (value),                                                                \
        struct monad_async_task_impl *: (void                                   \
                                             *)(((uintptr_t)(value)) |          \
                                                io_uring_user_data_type_task),  \
        struct                                                                  \
            monad_async_io_status *: (void                                      \
                                          *)(((uintptr_t)(value)) |             \
                                             io_uring_user_data_type_iostatus), \
        uintptr_t: (void *)(((uintptr_t)(value)) |                              \
                            io_uring_user_data_type_magic))

#define io_uring_sqe_set_data(sqe, value, task)                                \
    io_uring_sqe_set_data((sqe), io_uring_mangle_into_data(value));            \
    assert(((sqe)->user_data & 7) != 0);                                       \
    assert(                                                                    \
        ((sqe)->user_data & 7) == io_uring_user_data_type_magic ||             \
        ((uintptr_t)(value)) == ((sqe)->user_data & ~(uintptr_t)7));           \
    _Generic(                                                                  \
        (value),                                                               \
        default: (void)0,                                                      \
        struct monad_async_io_status *: io_uring_set_up_io_status(             \
                                          (struct monad_async_io_status        \
                                               *)(value),                      \
                                          (task)))

#define io_uring_cqe_get_data(task, iostatus, magic, cqe)                      \
    switch (((uintptr_t)io_uring_cqe_get_data(cqe)) & 7) {                     \
    default: {                                                                 \
        void *user_data = io_uring_cqe_get_data(cqe);                          \
        (void)user_data;                                                       \
        abort();                                                               \
    }                                                                          \
    case io_uring_user_data_type_task:                                         \
        (task) =                                                               \
            (struct monad_async_task_impl                                      \
                 *)(((uintptr_t)io_uring_cqe_get_data(cqe)) & ~(uintptr_t)7);  \
        (iostatus) = nullptr;                                                  \
        (magic) = 0;                                                           \
        break;                                                                 \
    case io_uring_user_data_type_iostatus:                                     \
        (task) = nullptr;                                                      \
        (iostatus) =                                                           \
            (struct monad_async_io_status                                      \
                 *)(((uintptr_t)io_uring_cqe_get_data(cqe)) & ~(uintptr_t)7);  \
        (magic) = 0;                                                           \
        break;                                                                 \
    case io_uring_user_data_type_magic:                                        \
        (task) = nullptr;                                                      \
        (iostatus) = nullptr;                                                  \
        (magic) = (uintptr_t)io_uring_cqe_get_data(cqe);                       \
        break;                                                                 \
    }

static inline void io_uring_set_up_io_status(
    struct monad_async_io_status *iostatus, struct monad_async_task_impl *task)
{
    iostatus->prev = iostatus->next = nullptr;
    iostatus->result.flags = (unsigned)-1;
    *((struct monad_async_task_impl **)&iostatus->result) = task;
}

static inline void atomic_lock(atomic_int *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_lock(lock, __tsan_mutex_try_lock);
#endif
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
        lock, &expected, 1, memory_order_acq_rel, memory_order_relaxed)) {
        thrd_yield();
        expected = 0;
    }
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_lock(lock, __tsan_mutex_try_lock, 0);
#endif
}

static inline void atomic_unlock(atomic_int *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_unlock(lock, __tsan_mutex_try_lock);
#endif
    atomic_store_explicit(lock, 0, memory_order_release);
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_unlock(lock, __tsan_mutex_try_lock);
#endif
}

static inline int mutex_lock(mtx_t *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_lock(lock, __tsan_mutex_try_lock);
#endif
    int r = mtx_lock(lock);
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_lock(lock, __tsan_mutex_try_lock, 0);
#endif
    return r;
}

static inline int mutex_unlock(mtx_t *lock)
{
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_pre_unlock(lock, __tsan_mutex_try_lock);
#endif
    int r = mtx_unlock(lock);
#if MONAD_ASYNC_HAVE_TSAN
    __tsan_mutex_post_unlock(lock, __tsan_mutex_try_lock);
#endif
    return r;
}

static inline int64_t timespec_to_ns(const struct timespec *a)
{
    return ((int64_t)a->tv_sec * 1000000000LL) + (int64_t)a->tv_nsec;
}

static inline int64_t
timespec_diff(const struct timespec *a, const struct timespec *b)
{
    return timespec_to_ns(a) - timespec_to_ns(b);
}

static inline monad_async_result
monad_async_executor_create_impl_fill_registered_buffers(
    struct monad_async_executor_impl_registered_buffers_t *p,
    unsigned buffers_small, unsigned buffers_large)
{
    p->size = buffers_small + buffers_large;
    if (p->size == 0) {
        return monad_async_make_success(0);
    }
    p->buffers = calloc(p->size, sizeof(struct iovec));
    if (p->buffers == nullptr) {
        return monad_async_make_failure(errno);
    }
    struct iovec *iov = p->buffers;
    if (buffers_small > 0) {
        void *mem = mmap(
            nullptr,
            buffers_small * 4096,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0);
        if (mem == MAP_FAILED) {
            return monad_async_make_failure(errno);
        }
        for (unsigned n = 0; n < buffers_small; n++) {
            iov->iov_base = (char *)mem + n * 4096;
            iov->iov_len = 4096;
            struct monad_async_executor_free_registered_buffer *i =
                (struct monad_async_executor_free_registered_buffer *)
                    iov->iov_base;
            iov++;
            i->index = (unsigned)(iov - p->buffers);
            i->next = p->free[0];
            p->free[0] = i;
        }
    }
    if (buffers_large > 0) {
        void *mem = mmap(
            nullptr,
            buffers_large * 2 * 1024 * 1024,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB |
                (21 << MAP_HUGE_SHIFT) /* 2Mb pages */,
            -1,
            0);
        if (mem == MAP_FAILED) {
            return monad_async_make_failure(errno);
        }
        for (unsigned n = 0; n < buffers_large; n++) {
            iov->iov_base = (char *)mem + n * 2 * 1024 * 1024;
            iov->iov_len = 2 * 1024 * 1024;
            struct monad_async_executor_free_registered_buffer *i =
                (struct monad_async_executor_free_registered_buffer *)
                    iov->iov_base;
            iov++;
            i->index = (unsigned)(iov - p->buffers);
            i->next = p->free[1];
            p->free[1] = i;
        }
    }
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_create_impl(
    struct monad_async_executor_impl *p, struct monad_async_executor_attr *attr)
{
    p->owning_thread = thrd_current();
    p->eventfd = eventfd(0, EFD_CLOEXEC);
    if (-1 == p->eventfd) {
        return monad_async_make_failure(errno);
    }
    if (attr->io_uring_ring.entries > 0) {
        int r = io_uring_queue_init_params(
            attr->io_uring_ring.entries, &p->ring, &attr->io_uring_ring.params);
        if (r < 0) {
            return monad_async_make_failure(-r);
        }
        if (attr->io_uring_wr_ring.entries > 0) {
            r = io_uring_queue_init_params(
                attr->io_uring_wr_ring.entries,
                &p->wr_ring,
                &attr->io_uring_wr_ring.params);
            if (r < 0) {
                return monad_async_make_failure(-r);
            }
        }
        if (!(p->ring.features & IORING_FEAT_NODROP)) {
            fprintf(
                stderr,
                "FATAL: This kernel's io_uring implementation does not "
                "implement "
                "no-drop.\n");
            abort();
        }
        if (!(p->ring.features & IORING_FEAT_SUBMIT_STABLE)) {
            fprintf(
                stderr,
                "FATAL: This kernel's io_uring implementation does not "
                "implement "
                "stable submits.\n");
            abort();
        }
        struct io_uring_sqe *sqe = io_uring_get_sqe(&p->ring);
        if (sqe == nullptr) {
            abort(); // should never occur
        }
        io_uring_prep_poll_multishot(sqe, p->eventfd, POLLIN);
        io_uring_sqe_set_data(
            sqe, EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC, nullptr);
        r = io_uring_submit(&p->ring);
        if (r < 0) {
            return monad_async_make_failure(-r);
        }
        MONAD_ASYNC_TRY_RESULT(
            ,
            monad_async_executor_create_impl_fill_registered_buffers(
                &p->registered_buffers[0],
                attr->io_uring_ring.registered_buffers.small,
                attr->io_uring_ring.registered_buffers.large));
        if (p->registered_buffers[0].size > 0) {
            r = io_uring_register_buffers(
                &p->ring,
                p->registered_buffers[0].buffers,
                p->registered_buffers[0].size);
            if (r < 0) {
                return monad_async_make_failure(-r);
            }
        }
        MONAD_ASYNC_TRY_RESULT(
            ,
            monad_async_executor_create_impl_fill_registered_buffers(
                &p->registered_buffers[1],
                attr->io_uring_wr_ring.registered_buffers.small,
                attr->io_uring_wr_ring.registered_buffers.large));
        if (p->registered_buffers[1].size > 0) {
            r = io_uring_register_buffers(
                &p->wr_ring,
                p->registered_buffers[1].buffers,
                p->registered_buffers[1].size);
            if (r < 0) {
                return monad_async_make_failure(-r);
            }
        }
    }
    return monad_async_make_success(0);
}

static inline monad_async_result
monad_async_executor_destroy_impl(struct monad_async_executor_impl *ex)
{
    if (!thrd_equal(thrd_current(), ex->owning_thread)) {
        fprintf(
            stderr,
            "FATAL: You must destroy an executor from the same kernel thread "
            "which owns it.\n");
        abort();
    }
    // Any tasks still executing must be cancelled
    atomic_lock(&ex->lock);
    for (monad_async_priority priority = monad_async_priority_high;
         priority < monad_async_priority_max;
         priority++) {
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_pending_launch[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_running[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_suspended_awaiting[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_suspended_completed[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            MONAD_ASYNC_TRY_RESULT(
                , monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
    }
    atomic_unlock(&ex->lock);
    if (ex->wr_ring.ring_fd != 0) {
        io_uring_queue_exit(&ex->wr_ring);
    }
    if (ex->ring.ring_fd != 0) {
        io_uring_queue_exit(&ex->ring);
    }
    if (ex->eventfd != -1) {
        close(ex->eventfd);
        ex->eventfd = -1;
    }
    for (unsigned n = 0; n < ex->registered_buffers[0].size; n++) {
        (void)munmap(
            ex->registered_buffers[0].buffers[n].iov_base,
            ex->registered_buffers[0].buffers[n].iov_len);
    }
    if (ex->registered_buffers[0].buffers != nullptr) {
        free(ex->registered_buffers[0].buffers);
    }
    for (unsigned n = 0; n < ex->registered_buffers[1].size; n++) {
        (void)munmap(
            ex->registered_buffers[1].buffers[n].iov_base,
            ex->registered_buffers[1].buffers[n].iov_len);
    }
    if (ex->registered_buffers[1].buffers != nullptr) {
        free(ex->registered_buffers[1].buffers);
    }
    return monad_async_make_success(0);
}

static inline monad_async_result monad_async_executor_wake_impl(
    atomic_int * /*lock must be held on entry*/,
    struct monad_async_executor_impl *ex,
    monad_async_result const *cause_run_to_return)
{
    if (cause_run_to_return != nullptr) {
        ex->cause_run_to_return_value = *cause_run_to_return;
        atomic_store_explicit(
            &ex->cause_run_to_return,
            &ex->cause_run_to_return_value,
            memory_order_release);
    }
    atomic_store_explicit(
        &ex->need_to_empty_eventfd, true, memory_order_release);
    if (-1 == eventfd_write(ex->eventfd, 1)) {
        return monad_async_make_success(errno);
    }
    return monad_async_make_success(0);
}

static inline struct io_uring_sqe *get_sqe_suspending_if_necessary(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    if (ex == nullptr ||
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) !=
            &task->head) {
        fprintf(
            stderr,
            "FATAL: Suspending operation invoked not by the "
            "current task executing.\n");
        abort();
    }
    assert(ex->within_run == true);
    assert(ex->ring.ring_fd != 0); // was the ring created?
    struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->ring);
    if (sqe == nullptr) {
        fprintf(
            stderr,
            "TODO: Handle SQE exhaustation via suspend until free SQE "
            "entries appear.\n");
        abort();
    }
    switch (task->head.priority.io) {
    default:
        break;
    case monad_async_priority_high:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case monad_async_priority_low:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    }
    return sqe;
}

static inline struct io_uring_sqe *get_wrsqe_suspending_if_necessary(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    if (ex == nullptr ||
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) !=
            &task->head) {
        fprintf(
            stderr,
            "FATAL: Suspending operation invoked not by the "
            "current task executing.\n");
        abort();
    }
    assert(ex->within_run == true);
    assert(ex->wr_ring.ring_fd != 0); // was the write ring created?
    struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->wr_ring);
    if (sqe == nullptr) {
        fprintf(
            stderr,
            "TODO: Handle SQE exhaustation via suspend until free SQE "
            "entries appear.\n");
        abort();
    }
    switch (task->head.priority.io) {
    default:
        break;
    case monad_async_priority_high:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case monad_async_priority_low:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    }
    // The write ring must always complete the preceding operation before it
    // initiates the next operation
    sqe->flags |= IOSQE_IO_DRAIN;
    ex->wr_ring_ops_outstanding++;
    return sqe;
}

static inline unsigned monad_async_executor_alloc_file_index(
    struct monad_async_executor_impl *ex, monad_async_file fh)
{
    if (ex->file_indices == nullptr) {
        ex->file_indices = calloc(4, sizeof(monad_async_file));
        if (ex->file_indices == nullptr) {
            return (unsigned)-1;
        }
        ex->file_indices_size = 4;
        memset(ex->file_indices, 0xff, 4 * sizeof(int));
        int r = io_uring_register_files(
            &ex->ring, (int const *)ex->file_indices, 4);
        if (r < 0) {
            fprintf(
                stderr,
                "FATAL: io_uring_register_files fails with '%s'\n",
                strerror(-r));
            abort();
        }
        if (ex->wr_ring.ring_fd != 0) {
            r = io_uring_register_files(
                &ex->wr_ring, (int const *)ex->file_indices, 4);
            if (r < 0) {
                fprintf(
                    stderr,
                    "FATAL: io_uring_register_files (write ring) fails with "
                    "'%s'\n",
                    strerror(-r));
                abort();
            }
        }
        memset(ex->file_indices, 0, 4 * sizeof(int));
    }
    for (unsigned n = 0; n < ex->file_indices_size; n++) {
        if (ex->file_indices[n] == nullptr) {
            ex->file_indices[n] = fh;
            return n;
        }
    }
    monad_async_file **new_file_indices = realloc(
        ex->file_indices, 2 * ex->file_indices_size * sizeof(monad_async_file));
    if (new_file_indices == nullptr) {
        return (unsigned)-1;
    }
    int *updlist = (int *)(ex->file_indices + ex->file_indices_size);
    memset(updlist, 0xff, ex->file_indices_size * sizeof(int));
    int r = io_uring_register_files_update(
        &ex->ring, ex->file_indices_size, updlist, ex->file_indices_size);
    if (r < 0) {
        fprintf(
            stderr,
            "FATAL: io_uring_register_files_update fails with '%s'\n",
            strerror(-r));
        abort();
    }
    if (ex->wr_ring.ring_fd != 0) {
        r = io_uring_register_files_update(
            &ex->wr_ring,
            ex->file_indices_size,
            updlist,
            ex->file_indices_size);
        if (r < 0) {
            fprintf(
                stderr,
                "FATAL: io_uring_register_files_update (write ring) fails with "
                "'%s'\n",
                strerror(-r));
            abort();
        }
    }
    memset(
        new_file_indices + ex->file_indices_size,
        0,
        ex->file_indices_size * sizeof(monad_async_file));
    unsigned ret = ex->file_indices_size;
    ex->file_indices_size *= 2;
    return ret;
}

static inline void monad_async_executor_free_file_index(
    struct monad_async_executor_impl *ex, unsigned file_index,
    monad_async_file fh)
{
    (void)fh;
    assert(file_index < ex->file_indices_size);
    assert(ex->file_indices[file_index] == fh);
    ex->file_indices[file_index] = nullptr;
}
