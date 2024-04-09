cmake_minimum_required(VERSION 3.5)

project(new-executor LANGUAGES C CXX)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)

add_library(monad_async STATIC
  "src/monad/async/executor.c"
  "src/monad/async/result.cpp"
  "src/monad/async/task.c"
)
target_compile_features(monad_async PUBLIC c_std_23 cxx_std_20)
target_include_directories(monad_async PUBLIC "include")
target_link_libraries(monad_async PUBLIC uring Boost::boost)

if(BINDGEN_PROGRAM)
  make_directory("${CMAKE_SOURCE_DIR}/rust")
  add_custom_command(TARGET monad_async POST_BUILD
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_SOURCE_DIR}/rust/async.rs" "${CMAKE_SOURCE_DIR}/include/monad/async/executor.h"
    --allowlist-function "monad_async.*"
    --allowlist-type "monad_async.*"
  )
endif()

add_executable(monad_async_test "test/async/executor.cpp")
target_link_libraries(monad_async_test PRIVATE monad_async GTest::GTest GTest::Main)
