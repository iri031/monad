function(monad_test target)
  add_executable(${target} ${ARGN})
  target_link_libraries(${target} PRIVATE monad_async GTest::GTest GTest::Main)
  target_link_options(${target} PRIVATE -rdynamic)
  add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>)
endfunction()

monad_test(monad_async_context_switcher_test "async/context_switcher.cpp")

monad_test(monad_async_executor_test "async/executor.cpp")

monad_test(monad_async_file_io_test "async/file_io.cpp")

monad_test(monad_async_monad_fiber_test "async/monad_fiber.cpp")

monad_test(monad_async_socket_io_test "async/socket_io.cpp")

monad_test(monad_async_work_dispatcher_test "async/work_dispatcher.cpp")

add_subdirectory("fiber")
