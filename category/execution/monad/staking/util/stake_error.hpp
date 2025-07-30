#pragma once

#pragma once

#include <category/core/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>

MONAD_NAMESPACE_BEGIN

enum class StakeError
{
    Success = 0,
    InternalError,
    MethodNotSupported,
    InvalidInput,
    ValidatorExists,
    UnknownValidator,
    UnknownDelegator,
    WithdrawalIdExists,
    UnknownWithdrawalId,
    WithdrawalNotReady,
    InsufficientStake,
    InvalidSecpPubkey,
    InvalidBlsPubkey,
    InvalidSecpSignature,
    InvalidBlsSignature,
    SecpSignatureVerificationFailed,
    BlsSignatureVerificationFailed,
    BlockAuthorNotInSet,
};

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::StakeError>
    : quick_status_code_from_enum_defaults<monad::StakeError>
{
    static constexpr auto const domain_name = "Stake Error";
    static constexpr auto const domain_uuid =
        "322cbaa5-e066-4b70-924f-82a0268e23e3";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
