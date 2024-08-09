#pragma once

#include <cstdarg>

#include <monad/config.hpp>
#include <monad/core/dump.h>

MONAD_NAMESPACE_BEGIN

class raii_dump_ctx {
public:
    raii_dump_ctx() = delete;

    raii_dump_ctx(monad_dump_ctx_t *parent) noexcept {
        monad_dump_ctx_push(&ctx_, parent);
    }

    raii_dump_ctx(monad_dump_ctx_t *parent, const char *format, ...) noexcept
    {
        std::va_list ap;
        va_start(ap, format);
        monad_dump_vprintln(parent, format, ap);
        va_end(ap);
        monad_dump_ctx_push(&ctx_, parent);
    }

    raii_dump_ctx(const raii_dump_ctx&) = delete;
    raii_dump_ctx(raii_dump_ctx&&) = delete;

    ~raii_dump_ctx() {
        monad_dump_ctx_pop(&ctx_);
    }

    monad_dump_ctx_t *get() const { return &ctx_; }

private:
    mutable monad_dump_ctx_t ctx_;
};

MONAD_NAMESPACE_END