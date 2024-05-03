
add_executable(monad_fiber_tests fcontext.cpp scheduler.cpp fiber.cpp task.cpp)
target_link_libraries(monad_fiber_tests PUBLIC monad_fiber GTest::GTest GTest::gtest_main)
add_test(NAME monad_fiber_tests COMMAND monad_fiber_tests)