(rule
 (targets demo.v)
 (alias test_ast)
 (deps (:input demo.cpp))
 (action
  (run cpp2v -v %{input} --no-elaborate -o demo.v
             -- -stdlib=libc++ -Xclang -internal-isystem -Xclang /usr/lib/llvm-18/bin/../include/c++/v1 -Xclang -internal-isystem -Xclang /usr/lib/llvm-18/lib/clang/18/include -Xclang -internal-isystem -Xclang /usr/local/include -Xclang -internal-isystem -Xclang /usr/lib/gcc/x86_64-linux-gnu/14/../../../../x86_64-linux-gnu/include -Xclang -internal-externc-isystem -Xclang /usr/include/x86_64-linux-gnu -Xclang -internal-externc-isystem -Xclang /include -Xclang -internal-externc-isystem -Xclang /usr/include )))

(alias (name srcs) (deps demo.cpp))
(rule
 (targets demo2.v)
 (alias test_ast)
 (deps (:input demo2.cpp))
 (action
  (run cpp2v -v %{input} --no-elaborate -o demo2.v
             -- -stdlib=libc++ -Xclang -internal-isystem -Xclang /usr/lib/llvm-18/bin/../include/c++/v1 -Xclang -internal-isystem -Xclang /usr/lib/llvm-18/lib/clang/18/include -Xclang -internal-isystem -Xclang /usr/local/include -Xclang -internal-isystem -Xclang /usr/lib/gcc/x86_64-linux-gnu/14/../../../../x86_64-linux-gnu/include -Xclang -internal-externc-isystem -Xclang /usr/include/x86_64-linux-gnu -Xclang -internal-externc-isystem -Xclang /include -Xclang -internal-externc-isystem -Xclang /usr/include )))

(alias (name srcs) (deps demo2.cpp))
(rule
 (targets demo3.v)
 (alias test_ast)
 (deps (:input demo3.cpp))
 (action
  (run cpp2v -v %{input} --no-elaborate -o demo3.v
             -- -stdlib=libc++ -Xclang -internal-isystem -Xclang /usr/lib/llvm-18/bin/../include/c++/v1 -Xclang -internal-isystem -Xclang /usr/lib/llvm-18/lib/clang/18/include -Xclang -internal-isystem -Xclang /usr/local/include -Xclang -internal-isystem -Xclang /usr/lib/gcc/x86_64-linux-gnu/14/../../../../x86_64-linux-gnu/include -Xclang -internal-externc-isystem -Xclang /usr/include/x86_64-linux-gnu -Xclang -internal-externc-isystem -Xclang /include -Xclang -internal-externc-isystem -Xclang /usr/include )))

(alias (name srcs) (deps demo3.cpp))
