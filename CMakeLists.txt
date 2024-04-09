cmake_minimum_required(VERSION 3.5)

project(new-executor LANGUAGES C CXX)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED)

add_library(monad_async STATIC
  "src/monad/async/executor.c"
  "src/monad/async/result.cpp"
  "src/monad/async/task.c"
)
target_compile_features(monad_async PUBLIC c_std_23 cxx_std_20)
target_include_directories(monad_async PUBLIC "include")
target_link_libraries(monad_async PUBLIC uring Boost::boost)

add_executable(monad_async_test "test/async/executor.cpp")
target_link_libraries(monad_async_test PRIVATE monad_async GTest::GTest GTest::Main)
