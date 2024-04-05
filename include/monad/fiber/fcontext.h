#pragma once

#include <stddef.h>

#if defined(BOOST_CONTEXT_DETAIL_FCONTEXT_H)

using boost::context::detail::jump_fcontext;
using boost::context::detail::make_fcontext;
using boost::context::detail::ontop_fcontext;

#else
#if defined(__cplusplus)
extern "C" {
#endif


typedef void*   fcontext_t;

struct transfer_t {
  fcontext_t  fctx;
  void    *   data;
};

struct transfer_t  jump_fcontext( fcontext_t const to, void * vp);
fcontext_t         make_fcontext( void * sp, size_t size, void (* fn)(struct  transfer_t) );
struct transfer_t ontop_fcontext( fcontext_t const to, void * vp, struct transfer_t (* fn)(struct  transfer_t) );



#if defined(__cplusplus)
}
#endif

#endif

#if __GNUC__ && !defined(__clang__)

#if defined(__SANITIZE_ADDRESS__)
#define MONAD_USE_ASAN 1
#endif

#if defined(__SANITIZE_THREAD__)
#define MONAD_USE_TSAN 1
#endif

#elif defined(__clang__)

#if __has_feature(address_sanitizer)
#define MONAD_USE_ASAN 1
#endif

#if __has_feature(thread_sanitizer)
#define MONAD_USE_TSAN 1
#else
#endif

#endif


/* note: if we do jump_fcontext the return is the one we get resumed from
  this poses a bit of a problem for symmetric transfers, because if we jump

  main -> fiber1 -> fiber2 then this will return a reference to fiber2.

  main:
    f = fiber1.resume()

*/