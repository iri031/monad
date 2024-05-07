#pragma once

#include <monad/core/result.hpp>
#include <monad/mpt/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/generic_code.hpp>)
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#endif

MONAD_MPT_NAMESPACE_BEGIN

enum class DbError : uint8_t
{
    unknown,
    root_node_is_null_failure,
    key_mismatch_failure,
    branch_not_exist_failure,
    key_ends_earlier_than_node_failure,
    node_is_not_leaf_failure,
    need_to_read_from_disk
};

MONAD_MPT_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<MONAD_MPT_NAMESPACE::DbError>
    : quick_status_code_from_enum_defaults<MONAD_MPT_NAMESPACE::DbError>
{
    static constexpr auto const domain_name = "DbError domain";

    static constexpr auto const domain_uuid =
        "{975a8e5e-d53f-4a57-304e-0dd4785b4090}";

    static std::initializer_list<mapping> const &value_mappings()
    {
        static std::initializer_list<mapping> const v = {
            {MONAD_MPT_NAMESPACE::DbError::root_node_is_null_failure,
             "root node is null",
             {}},
            {MONAD_MPT_NAMESPACE::DbError::key_mismatch_failure,
             "key mismatch",
             {}},
            {MONAD_MPT_NAMESPACE::DbError::branch_not_exist_failure,
             "branch node exist",
             {}},
            {MONAD_MPT_NAMESPACE::DbError::key_ends_earlier_than_node_failure,
             "key ends in the middle of a node path",
             {}},
            {MONAD_MPT_NAMESPACE::DbError::node_is_not_leaf_failure,
             "found a non-leaf node",
             {}},
            {MONAD_MPT_NAMESPACE::DbError::need_to_read_from_disk,
             "not found from cached nodes, need to read from disk",
             {}},
            {MONAD_MPT_NAMESPACE::DbError::unknown, "unknown", {}},
        };
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
