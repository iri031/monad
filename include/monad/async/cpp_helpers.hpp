#pragma once

// Needs to come before others, on clang <stdatomic.h> breaks <atomic>
#include <boost/outcome/experimental/status_result.hpp>

#include <liburing.h>

#include "all.h"

#include <memory>

namespace monad
{
    namespace async
    {
        using BOOST_OUTCOME_V2_NAMESPACE::experimental::errc;

        //! \brief Return a C result as a C++ result
        extern BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<intptr_t>
        to_result(monad_async_result r);

        //! \brief Throws any error in the result as a C++ exception
        [[noreturn]] extern void throw_exception(monad_async_result r);

        struct executor_deleter
        {
            void operator()(monad_async_executor ex) const
            {
                auto r = ::monad_async_executor_destroy(ex);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using executor_ptr =
            std::unique_ptr<monad_async_executor_head, executor_deleter>;

        //! \brief Construct an executor instance, and return it in a smart
        //! pointer
        executor_ptr make_executor(struct monad_async_executor_attr &attr)
        {
            monad_async_executor ex;
            auto r = monad_async_executor_create(&ex, &attr);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return executor_ptr(ex);
        }

        struct file_deleter
        {
            monad_async_task task;

            void operator()(monad_async_file ex) const
            {
                auto r = ::monad_async_task_file_destroy(task, ex);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using file_ptr = std::unique_ptr<monad_async_file_head, file_deleter>;

        //! \brief Construct a file instance, and return it in a smart
        //! pointer
        file_ptr make_file(
            monad_async_task task, monad_async_file base, char const *subpath,
            struct open_how &how)
        {
            monad_async_file ex;
            auto r =
                monad_async_task_file_create(&ex, task, base, subpath, &how);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return file_ptr(ex, file_deleter{task});
        }

        struct context_switcher_deleter
        {
            void operator()(monad_async_context_switcher t) const
            {
                auto r = ::monad_async_context_switcher_destroy(t);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using context_switcher_ptr = std::unique_ptr<
            monad_async_context_switcher_head, context_switcher_deleter>;

        //! \brief Construct a context switcher instance, and return it in a
        //! smart pointer
        context_switcher_ptr
        make_context_switcher(monad_async_context_switcher_impl impl)
        {
            monad_async_context_switcher ex;
            auto r = impl.create(&ex);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return context_switcher_ptr(ex);
        }

        struct context_deleter
        {
            monad_async_context_switcher switcher;

            void operator()(monad_async_context t) const
            {
                auto r = switcher->destroy(t);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using context_ptr =
            std::unique_ptr<monad_async_context_head, context_deleter>;

        //! \brief Construct a context instance, and return it in a
        //! smart pointer
        context_ptr make_context(
            monad_async_context_switcher impl, monad_async_task task,
            struct monad_async_task_attr &attr)
        {
            monad_async_context ex;
            auto r = impl->create(&ex, impl, task, &attr);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return context_ptr(ex, {impl});
        }

        struct socket_deleter
        {
            monad_async_task task;

            void operator()(monad_async_socket ex) const
            {
                auto r = ::monad_async_task_socket_destroy(task, ex);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using socket_ptr =
            std::unique_ptr<monad_async_socket_head, socket_deleter>;

        //! \brief Construct a socket instance, and return it in a smart
        //! pointer
        socket_ptr make_socket(
            monad_async_task task, int domain, int type, int protocol,
            unsigned flags)
        {
            monad_async_socket ex;
            auto r = monad_async_task_socket_create(
                &ex, task, domain, type, protocol, flags);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return socket_ptr(ex, socket_deleter{task});
        }

        struct task_deleter
        {
            void operator()(monad_async_task t) const
            {
                auto r = ::monad_async_task_destroy(t);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using task_ptr = std::unique_ptr<monad_async_task_head, task_deleter>;

        //! \brief Construct a task instance, and return it in a smart pointer
        task_ptr make_task(
            monad_async_context_switcher switcher,
            struct monad_async_task_attr &attr)
        {
            monad_async_task t;
            auto r = monad_async_task_create(&t, switcher, &attr);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return task_ptr(t);
        }

        struct work_dispatcher_deleter
        {
            void operator()(monad_async_work_dispatcher t) const
            {
                auto r = ::monad_async_work_dispatcher_destroy(t);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using work_dispatcher_ptr = std::unique_ptr<
            monad_async_work_dispatcher_head, work_dispatcher_deleter>;

        //! \brief Construct a work dispatcher instance, and return it in a
        //! smart pointer
        work_dispatcher_ptr
        make_work_dispatcher(struct monad_async_work_dispatcher_attr &attr)
        {
            monad_async_work_dispatcher t;
            auto r = monad_async_work_dispatcher_create(&t, &attr);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return work_dispatcher_ptr(t);
        }

        struct work_dispatcher_executor_deleter
        {
            void operator()(monad_async_work_dispatcher_executor t) const
            {
                auto r = ::monad_async_work_dispatcher_executor_destroy(t);
                if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                    throw_exception(r);
                }
            }
        };

        using work_dispatcher_executor_ptr = std::unique_ptr<
            monad_async_work_dispatcher_executor_head,
            work_dispatcher_executor_deleter>;

        //! \brief Construct a work dispatcher executor instance, and return it
        //! in a smart pointer
        work_dispatcher_executor_ptr make_work_dispatcher_executor(
            monad_async_work_dispatcher dp,
            struct monad_async_work_dispatcher_executor_attr &attr)
        {
            monad_async_work_dispatcher_executor t;
            auto r = monad_async_work_dispatcher_executor_create(&t, dp, &attr);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                throw_exception(r);
            }
            return work_dispatcher_executor_ptr(t);
        }
    }
}
