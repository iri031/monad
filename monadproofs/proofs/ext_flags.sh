#!/usr/bin/env bash
#
# ext_flags.sh: Extract system include flags from Clang.

set -euo pipefail

getSystemPaths() {
    local args=()
    while [[ $# -gt 0 ]]; do
        if [[ "$1" == "-isystem" ]]; then
            args+=("$1")
            shift
            if [[ $# -gt 0 ]]; then
                args+=("$1")
            fi
        elif [[ "$1" =~ ^-internal.*system.*$ ]]; then
            args+=("-Xclang")
            args+=("$1")
            shift
            if [[ $# -gt 0 ]]; then
                args+=("-Xclang")
                args+=("$1")
            fi
        fi
        shift
    done
    echo "${args[@]}"
}

if [[ $# -gt 0 ]]; then
    # If arguments are passed, parse them directly
    getSystemPaths "$@"
else
    # Extract Clang system includes in a safe way
    clang_args=$(clang++ -### -E -x c++ - < /dev/null 2>&1 | grep -Fv '(in-process)' | sed '5q;d')

    # Ensure Clang actually produced output
    if [[ -n "$clang_args" ]]; then
        # Use eval + set -- to properly split the command output into separate arguments
        eval set -- "$clang_args"
        getSystemPaths "$@"
    else
        exit 1  # Fail if Clang did not return expected output
    fi
fi
