#pragma once

#include <monad/config.hpp>
#include <monad/event/event_emitter.hpp>

#include <istream>
#include <optional>

MONAD_NAMESPACE_BEGIN

class AppendOnlyLogEmitter : public EventEmitter
{
    std::istream &cursor_;

public:
    AppendOnlyLogEmitter(
        std::istream &, monad_execution_event const * = nullptr);

    std::optional<Event> next_event() override;
};

MONAD_NAMESPACE_END
