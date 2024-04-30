enable_testing()

find_package(GTest REQUIRED)

add_executable(tests fcontext.cpp scheduler.cpp fiber.cpp current.cpp)
target_link_libraries(tests PUBLIC monad_fiber_sandbox GTest::gtest_main)
add_test(NAME tests COMMAND tests)