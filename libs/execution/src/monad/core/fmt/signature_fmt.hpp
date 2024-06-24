#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/core/signature.hpp>

#include <quill/Quill.h>

template <>
struct quill::copy_loggable<monad::SignatureAndChain> : std::true_type
{
};

template <>
struct fmt::formatter<monad::SignatureAndChain> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::SignatureAndChain const &sc, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "SignatureAndChain{{"
            "r={} "
            "s={} "
            "chain_id={} "
            "odd_y_parity={}"
            "}}",
            sc.r,
            sc.s,
            sc.chain_id,
            sc.odd_y_parity);
        return ctx.out();
    }
};
