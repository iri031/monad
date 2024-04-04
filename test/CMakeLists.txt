enable_testing()

add_executable(fcontext fcontext.c)
add_test(NAME fcontext COMMAND fcontext)
target_link_libraries(fcontext PUBLIC monad_fiber_sandbox)
