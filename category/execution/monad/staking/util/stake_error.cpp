#include <category/execution/monad/staking/util/stake_error.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::StakeError>::mapping> const &
quick_status_code_from_enum<monad::StakeError>::value_mappings()
{
    using monad::StakeError;

    static std::initializer_list<mapping> const v = {
        {StakeError::Success, "success", {errc::success}},
        {StakeError::InternalError, "internal error", {}},
        {StakeError::MethodNotSupported, "overflow", {}},
        {StakeError::InvalidInput, "invalid input", {}},
        {StakeError::ValidatorExists, "validator exists", {}},
        {StakeError::UnknownValidator, "unknown validator", {}},
        {StakeError::UnknownDelegator, "unknown delegator", {}},
        {StakeError::WithdrawalIdExists, "withdrawal id exists", {}},
        {StakeError::UnknownWithdrawalId, "unknown withdrawal id", {}},
        {StakeError::WithdrawalNotReady, "withdrawal not ready", {}},
        {StakeError::InsufficientStake, "insufficient stake", {}},
        {StakeError::InvalidSecpPubkey, "invalid secp pubkey", {}},
        {StakeError::InvalidBlsPubkey, "invalid secp pubkey", {}},
        {StakeError::InvalidSecpSignature, "invalid secp signature", {}},
        {StakeError::InvalidBlsSignature, "invalid bls signature", {}},
        {StakeError::SecpSignatureVerificationFailed,
         "secp signature verification failed",
         {}},
        {StakeError::BlsSignatureVerificationFailed,
         "bls signature verification failed",
         {}},
        {StakeError::BlockAuthorNotInSet, "block author not in set", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
