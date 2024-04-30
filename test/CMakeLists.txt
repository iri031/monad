enable_testing()

function(monad_test target)
  add_executable(${target} ${ARGN})
  target_link_libraries(${target} PRIVATE monad_async GTest::GTest GTest::Main)
  target_link_options(${target} PRIVATE -rdynamic)
  add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>)
endfunction()

monad_test(monad_async_executor_test "async/executor.cpp")

monad_test(monad_async_file_io_test "async/file_io.cpp")

monad_test(monad_async_work_dispatcher_test "async/work_dispatcher.cpp")

if(TARGET monad_fiber)
  add_subdirectory("fiber")
endif()
