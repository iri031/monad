#!/usr/bin/env bash
#
# dune-gen.sh: Generate Dune rules for all .cpp/.hpp in the current directory,
# using system include flags from ext_flags.sh

set -euo pipefail

# 1) Get the system flags by calling ext_flags.sh
system_includes="$(./ext_flags.sh)"

# 2) Generate the rules
shopt -s nullglob

for src in *.cpp *.hpp; do
    base="${src%.*}"   # e.g. foo.cpp -> foo
    ext="${src##*.}"   # e.g. foo.cpp -> cpp

    # We'll produce a single .v file: foo_cpp.v
    cat <<EOF
(rule
 (targets ${base}.v)
 (alias test_ast)
 (deps (:input ${src}))
 (action
  (run cpp2v -v %{input} --no-elaborate -o ${base}.v
             -- -stdlib=libc++ ${system_includes} )))

(alias (name srcs) (deps ${src}))
EOF
done
