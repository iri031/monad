#!/bin/bash

getSystemPaths() {
    local args=()
    while [[ $# -gt 0 ]]; do
        if [[ "$1" =~ ^(-isystem)$ ]]; then
            args+=("${BASH_REMATCH[1]}")
            shift
            args+=("$1")
        elif [[ "$1" =~ ^(-internal.*system.*)$ ]]; then
            args+=("-Xclang")
            args+=("${BASH_REMATCH[1]}")
            shift
            args+=("-Xclang")
            args+=("$1")
        fi
        shift
    done
    echo "${args[@]}"
}

# If arguments are passed, process them
if [[ $# -gt 0 ]]; then
    getSystemPaths "$@"
else
    # Extract arguments from Clang's output
    clang++ -### -E -x c++ - < /dev/null 2>&1 | grep -Fv '(in-process)' | sed '5q;d' | xargs bash "$0"
fi
