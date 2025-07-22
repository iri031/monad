#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/validate_monad_block.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif

MONAD_NAMESPACE_BEGIN

template <class MonadConsensusBlockHeader>
Result<void> static_validate_consensus_header(
    MonadChain const &chain, MonadConsensusBlockHeader const &header)
{
    uint64_t const timestamp_s = uint64_t{header.timestamp_ns / 1'000'000'000};
    if (MONAD_UNLIKELY(timestamp_s != header.execution_inputs.timestamp)) {
        return MonadBlockError::TimestampMismatch;
    }

    auto const monad_rev = chain.get_monad_revision(0, timestamp_s);
    if (MONAD_LIKELY(monad_rev >= MONAD_THREE)) {
        if constexpr (!std::same_as<
                          MonadConsensusBlockHeader,
                          MonadConsensusBlockHeaderV1>) {
            return MonadBlockError::VersionRevisionMismatch;
        }
    }
    else {
        if constexpr (!std::same_as<
                          MonadConsensusBlockHeader,
                          MonadConsensusBlockHeaderV0>) {
            return MonadBlockError::VersionRevisionMismatch;
        }
    }
    return outcome::success();
}

EXPLICIT_MONAD_CONSENSUS_BLOCK_HEADER(static_validate_consensus_header);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::MonadBlockError>::mapping> const &
quick_status_code_from_enum<monad::MonadBlockError>::value_mappings()
{
    using monad::MonadBlockError;

    static std::initializer_list<mapping> const v = {
        {MonadBlockError::Success, "success", {errc::success}},
        {MonadBlockError::TimestampMismatch, "timestamp mismatch", {}},
        {MonadBlockError::VersionRevisionMismatch,
         "version revision mismatch",
         {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
