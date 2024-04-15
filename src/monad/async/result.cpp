#include "monad/async/config.h"

#include <boost/outcome/experimental/status_result.hpp>

extern "C" monad_async_result monad_async_make_success(intptr_t v)
{
    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<intptr_t> ret1(v);
    monad_async_result ret2;
    static_assert(sizeof(ret1) == sizeof(ret2));
    memcpy(&ret2, &ret1, sizeof(ret1));
    return ret2;
}

extern "C" monad_async_result monad_async_make_failure(int ec)
{
    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<intptr_t> ret1{
        BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code(ec)};
    monad_async_result ret2;
    static_assert(sizeof(ret1) == sizeof(ret2));
    memcpy(&ret2, &ret1, sizeof(ret1));
    return ret2;
}

namespace monad
{
    namespace async
    {
        [[noreturn]] extern void throw_exception(monad_async_result r)
        {
            union type_punner_t
            {
                monad_async_result c;
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>
                    cpp;

                constexpr type_punner_t() {}

                ~type_punner_t() {}
            } pun;

            pun.c = r;
            if (pun.cpp.has_error()) {
                pun.cpp.assume_error().throw_exception();
            }
            abort();
        }
    }
}
