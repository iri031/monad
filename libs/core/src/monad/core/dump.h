#pragma once

/**
 * @file
 *
 * printf-like interface for dumping structured data, either completely
 * unbuffered and using (mostly) async-signal-safe routines, or to buffered
 * libc-style streams for better performance
 */

#include <signal.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct monad_dump_backend monad_dump_backend_t;
typedef struct monad_dump_ctx monad_dump_ctx_t;

constexpr size_t MONAD_DUMP_CHECK_PTR_SMALL_SIZE = 64; // When printing <= 16
constexpr size_t MONAD_DUMP_CHECK_PTR_BIG_SIZE = 1024; // When printing up to 256 bytes

enum monad_dump_object_type {
    MONAD_DUMP_CTX,
    MONAD_DUMP_BACKEND_STREAM,
    MONAD_DUMP_BACKEND_FD
};

struct monad_dump_ctx {
    enum monad_dump_object_type object_type;
    monad_dump_backend_t *backend;
    unsigned indent_incr;
    unsigned max_field_length;
    const monad_dump_ctx_t *prev_ctx;
};

struct monad_dump_backend {
    enum monad_dump_object_type object_type;
    unsigned leading_indent;
    unsigned indent_incr;
    union {
        int fd;
        FILE *stream;
    };
    bool at_start_of_line;
    monad_dump_ctx_t root_ctx;
};

monad_dump_ctx_t *monad_dump_backend_init_fd(monad_dump_backend_t *dump_be,
                                             unsigned indent_incr, int fd);

monad_dump_ctx_t *monad_dump_backend_init_stream(monad_dump_backend_t *dump_be,
                                                 unsigned indent_incr,
                                                 FILE *stream);

monad_dump_ctx_t *monad_dump_ctx_push(monad_dump_ctx_t *push,
                                      const void *parent);

monad_dump_ctx_t *monad_dump_ctx_pop(monad_dump_ctx_t *pop);

void monad_dump_siginfo(monad_dump_ctx_t *ctx, const siginfo_t *siginfo,
                        ucontext_t *uc);

void monad_dump_vprintf(monad_dump_ctx_t *ctx, const char *format, va_list ap);

static inline void
monad_dump_printf(monad_dump_ctx_t *ctx, const char *format, ...) {
    va_list ap;
    va_start(ap, format);
    monad_dump_vprintf(ctx, format, ap);
    va_end(ap);
}

static inline void
monad_dump_vprintln(monad_dump_ctx_t *ctx, const char *format, va_list ap) {
    monad_dump_vprintf(ctx, format, ap);
    monad_dump_printf(ctx, "\n");
}

static inline void
monad_dump_println(monad_dump_ctx_t *ctx, const char *format, ...) {
    va_list ap;
    va_start(ap, format);
    monad_dump_vprintf(ctx, format, ap);
    va_end(ap);
    monad_dump_printf(ctx, "\n");
}

void monad_dump_vprintf_field(monad_dump_ctx_t *ctx, const char *field_name,
                              const char *format, va_list ap);

static inline void
monad_dump_printf_field(monad_dump_ctx_t *ctx, const char *field_name,
                        const char *format, ...) {
    va_list ap;
    va_start(ap, format);
    monad_dump_vprintf_field(ctx, field_name, format, ap);
    va_end(ap);
}

/// Prints the value of a pointer, followed by `n` number of bytes present at
/// that address; this is slow but is safe to call if `p` is an invalid pointer:
/// it will first query the current memory map before trying to access the
/// memory and will report if the associated memory pages are unmapped
const char *monad_dump_check_and_deref_ptr(const void *p, uint8_t n, char *buf,
                                           size_t len);

#ifdef __cplusplus
} // extern "C"
#endif
