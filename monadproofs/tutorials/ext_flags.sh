#!/usr/bin/env bash
#
# ext_flags.sh: Extract system include flags from Clang, ensuring -stdlib=libc++ works.

set -euo pipefail

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

# 1) Capture all lines from Clang's verbose driver output with -stdlib=libc++
clang_out="$(clang++ -### -E -x c++ -stdlib=libc++ - < /dev/null 2>&1 || true)"

# 2) Remove any lines mentioning '(in-process)'
clang_out="$(echo "$clang_out" | grep -Fv '(in-process)' || true)"

# 3) Extract everything inside "double quotes" from all lines
mapfile -t quoted_lines < <(echo "$clang_out" | grep -oE '"[^"]+"')

# 4) Strip the surrounding quotes and store in an array
tokens=()
for item in "${quoted_lines[@]}"; do
    no_quotes="${item#\"}"  # remove first quote
    no_quotes="${no_quotes%\"}" # remove last quote
    tokens+=( "$no_quotes" )
done

# 5) Pass these tokens to getSystemPaths
getSystemPaths "${tokens[@]}"
