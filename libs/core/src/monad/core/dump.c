#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#include <libunwind/libunwind.h>

#include <monad/core/assert.h>
#include <monad/core/dump.h>

static const char SPACES[] = "                ";

static inline bool
try_snprintf(char **buf, size_t *len, const char *format, ...) {
    va_list ap;
    int written;

    va_start(ap, format);
    written = vsnprintf(*buf, *len, format, ap);
    va_end(ap);
    if (written < 0) {
        (*buf)[0] = '\0';
        return false;
    }
    if ((size_t)written > *len) {
        written = *len;
        (*buf)[written - 1] = '\0';
    }
    *len -= written;
    *buf += written;
    return true;
}

static void dump_fd_vprintf(monad_dump_backend_t *dump_be, const char *format,
                            va_list ap) {
    char msg_buf[4096];
    char err_buf[128];
    int msg_len;
    int err_len;
    div_t space_div;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-result"
    if (dump_be->at_start_of_line) {
        space_div = div((int)dump_be->leading_indent, sizeof SPACES - 1);
        for (int i = 0; i < space_div.quot; ++i)
            (void)write(dump_be->fd, SPACES, sizeof SPACES - 1);
        (void)write(dump_be->fd, SPACES, space_div.rem);
        dump_be->at_start_of_line = false;
    }
    msg_len = vsnprintf(msg_buf, sizeof msg_buf, format, ap);
    if (msg_len < 0)
        return;
    else if ((size_t)msg_len >= sizeof msg_buf) {
        strcpy(msg_buf + sizeof msg_buf - sizeof "<truncated>", "<truncated>");
        msg_len = sizeof msg_buf - 1;
    }
    if (write(dump_be->fd, msg_buf, msg_len) == -1) {
        err_len = snprintf(err_buf, sizeof err_buf,
                           "could not write msg to fd %d: %s (%d) -- msg content:\n",
                           dump_be->fd, strerror(errno), errno);
        (void)write(STDERR_FILENO, err_buf, err_len);
        (void)write(STDERR_FILENO, msg_buf, msg_len);
    }
#pragma GCC diagnostic pop
}

static void dump_stream_vprintf(monad_dump_backend_t *dump_be,
                                const char *format, va_list ap) {
    div_t space_div;

    if (dump_be->at_start_of_line) {
        space_div = div((int)dump_be->leading_indent, sizeof SPACES - 1);
        for (int i = 0; i < space_div.quot; ++i)
            fprintf(dump_be->stream, SPACES);
        fprintf(dump_be->stream, "%.*s", space_div.rem, SPACES);
        dump_be->at_start_of_line = false;
    }
    vfprintf(dump_be->stream, format, ap);
}

monad_dump_ctx_t *monad_dump_backend_init_fd(monad_dump_backend_t *dump_be,
                                             unsigned indent_incr, int fd) {
    MONAD_DEBUG_ASSERT(dump_be != nullptr && fd >= 0);
    dump_be->object_type = MONAD_DUMP_BACKEND_FD;
    dump_be->leading_indent = 0;
    dump_be->indent_incr = indent_incr;
    dump_be->fd = fd;
    dump_be->at_start_of_line = true;
    return monad_dump_ctx_push(&dump_be->root_ctx, dump_be);
}

monad_dump_ctx_t *monad_dump_backend_init_stream(monad_dump_backend_t *dump_be,
                                                 unsigned indent_incr,
                                                 FILE *stream) {
    MONAD_DEBUG_ASSERT(dump_be != nullptr && stream != nullptr);
    dump_be->object_type = MONAD_DUMP_BACKEND_STREAM;
    dump_be->leading_indent = 0;
    dump_be->indent_incr = indent_incr;
    dump_be->stream = stream;
    dump_be->at_start_of_line = true;
    return monad_dump_ctx_push(&dump_be->root_ctx, dump_be);
}

monad_dump_ctx_t *monad_dump_ctx_push(monad_dump_ctx_t *push,
                                      const void *parent) {
    MONAD_DEBUG_ASSERT(push != nullptr && parent != nullptr);

    push->object_type = MONAD_DUMP_CTX;
    switch (*(const enum monad_dump_object_type*)parent) {
    case MONAD_DUMP_CTX:
        push->prev_ctx = (const monad_dump_ctx_t*)parent;
        push->backend = push->prev_ctx->backend;
        push->indent_incr = push->backend->indent_incr;
        break;

    case MONAD_DUMP_BACKEND_FD:
        [[fallthrough]];
    case MONAD_DUMP_BACKEND_STREAM:
        push->prev_ctx = nullptr;
        push->backend = (monad_dump_backend_t*)parent;
        push->indent_incr = 0;
        break;
    }

    push->backend->leading_indent += push->indent_incr;
    return push;
}

monad_dump_ctx_t *monad_dump_ctx_pop(monad_dump_ctx_t *pop) {
    MONAD_DEBUG_ASSERT(pop != nullptr &&
                       pop->backend->leading_indent >= pop->indent_incr);
    pop->backend->leading_indent -= pop->indent_incr;
    return (monad_dump_ctx_t*)pop->prev_ctx;
}

void monad_dump_siginfo(monad_dump_ctx_t *ctx, const siginfo_t *siginfo,
                        void *ucontext) {
    (void)ucontext; // XXX: not currently used
    ctx->max_field_length = sizeof "si_addr_lsb" - 1;

    monad_dump_printf_field(ctx, "si_signo", "%d", siginfo->si_signo);
    monad_dump_printf_field(ctx, "si_code", "%d", siginfo->si_code);
    monad_dump_printf_field(ctx, "si_pid", "%d", siginfo->si_pid);
    monad_dump_printf_field(ctx, "si_uid", "%d", siginfo->si_uid);

    switch (siginfo->si_signo) {
    case SIGSEGV:
    case SIGBUS:
        monad_dump_printf_field(ctx, "si_addr", "%p", siginfo->si_addr);
        monad_dump_printf_field(ctx, "si_addr_lsb", "%hd",
                                siginfo->si_addr_lsb);
        break;
    }
}

[[gnu::noinline]] void monad_dump_stacktrace(monad_dump_ctx_t *ctx) {
    constexpr unsigned MAX_FRAMES = 256;
    unw_context_t context;
    unw_cursor_t cursor;
    unw_word_t offset, ip;
    char fnbuf[64];
    int frame = 0;
    int rc;

    (void)unw_getcontext(&context);
    (void)unw_init_local(&cursor, &context);

    while ((rc = unw_step(&cursor)) > 0) {
        unw_get_reg(&cursor, UNW_REG_IP, &ip);
        rc = unw_get_proc_name(&cursor, fnbuf, sizeof fnbuf, &offset);
        if (rc != UNW_ESUCCESS)
            monad_dump_println(ctx, "%02d: %p in ??: %d", frame, ip, rc);
        else
            monad_dump_println(ctx, "%02d: %p in %s+%p", frame, ip, fnbuf, offset);
        if (frame++ == MAX_FRAMES) {
            // Because fiber stack corruption is likely to lead to bouncing
            // around aimlessly, we impose a maximum length to the iterative
            // stack trace
            monad_dump_println(ctx, "aborting stack trace after %d frames",
                               frame);
            return;
        }
    }
    if (rc < 0)
        monad_dump_println(ctx, "uwn_step(3) stack trace ended early: %d", rc);
}

void monad_dump_vprintf(monad_dump_ctx_t *ctx, const char *format, va_list ap) {
    MONAD_DEBUG_ASSERT(ctx != nullptr && format != nullptr);
    size_t format_len;
    if (ctx->backend->object_type == MONAD_DUMP_BACKEND_FD)
        dump_fd_vprintf(ctx->backend, format, ap);
    else if (ctx->backend->object_type == MONAD_DUMP_BACKEND_STREAM)
        dump_stream_vprintf(ctx->backend, format, ap);
    else {
        fprintf(stderr, "fatal: unknown backend type %d\n", ctx->object_type);
        abort();
    }
    if (format != nullptr && (format_len = strlen(format)) > 0)
        ctx->backend->at_start_of_line = format[format_len - 1] == '\n';
}

void monad_dump_vprintf_field(monad_dump_ctx_t *ctx, const char *field_name,
                              const char *format, va_list ap) {
    if (format == nullptr)
        return monad_dump_println(ctx, field_name);
    if (ctx->max_field_length == 0)
        monad_dump_printf(ctx, "%s: ", field_name);
    else
        monad_dump_printf(ctx, "%-*s : ", (int)ctx->max_field_length,
                          field_name);
    monad_dump_vprintln(ctx, format, ap);
}

const char *monad_dump_check_and_deref_ptr(const void *p, uint8_t n, char *buf,
                                           size_t len)
{
    unsigned char vec[2];
    int page_size;
    uintptr_t map_base;
    size_t mapped_length;
    char *next = buf;

    if (!try_snprintf(&next, &len, "%p", p))
        return buf;

    if (p == nullptr)
        return buf; // If it's nullptr, don't print anything extra

    // Find which memory page (or pair of pages, if we cross a page boundary)
    // contains our data
    page_size = getpagesize();
    if (page_size == -1) {
        // Couldn't find out the page size
        (void)snprintf(next, len, " : [??:PS:%d]", errno);
        return buf;
    }
    map_base = (uintptr_t)p & ~((size_t)page_size - 1ULL);
    mapped_length = (size_t)page_size;
    if ((uintptr_t)p + n > map_base + page_size)
        mapped_length += page_size; // Access crosses into next page

    // TODO(ken): this is a little nicer than doing any system-specific stuff
    //   since mincore(2) is somewhat portable and because the Linux interface
    //   for doing this the real way is horrible (i.e., parsing proc(5)). But
    //   we can't tell if it's safe to actually touch the pages or not, e.g.,
    //   our PROT_NONE stack guard pages are "in core" but will segfault if read
    if (mincore((void*)map_base, mapped_length, vec) == -1) {
        switch (errno) {
        case ENOMEM:
            (void)snprintf(next, len, " : [UNMAPPED]");
            return buf;
        default:
            (void)snprintf(next, len, " : [??:MIC:%d]", errno);
            return buf;
        }
    }

    if (n == 0)
        return buf;

    // Memory appears safe to deference, copy it out
    if (!try_snprintf(&next, &len, " : "))
        return buf;
    for (uint8_t i = 0; i < n; ++i) {
        if (!try_snprintf(&next, &len, "%02hhx", *((uint8_t*)p + i)))
            break;
    }
    return buf;
}