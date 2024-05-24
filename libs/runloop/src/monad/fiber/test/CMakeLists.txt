
add_executable(monad_fiber_c_tests fcontext.cpp scheduler.cpp fiber.cpp task.cpp current.cpp)
target_link_libraries(monad_fiber_c_tests PUBLIC monad_fiber_c GTest::GTest GTest::gtest_main)
gtest_discover_tests(
  monad_fiber_c_tests
  TEST_PREFIX RunLoop/
  PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
             UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
             TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
