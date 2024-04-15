cmake_minimum_required(VERSION 3.5)

project(new-executor LANGUAGES C CXX)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)

add_library(monad_async STATIC
  "src/monad/async/context_switcher_none.c"
  "src/monad/async/context_switcher_sjlj.c"
  "src/monad/async/executor.c"
  "src/monad/async/result.cpp"
  "src/monad/async/task.c"
  "src/monad/async/work_dispatcher.c"
)
target_compile_features(monad_async PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_async PUBLIC -Wall -Wextra -Wconversion -Wpedantic)
target_include_directories(monad_async PUBLIC "include")
target_link_libraries(monad_async PUBLIC uring Boost::boost)

if(BINDGEN_PROGRAM)
  make_directory("${CMAKE_SOURCE_DIR}/rust")
  add_custom_command(OUTPUT "${CMAKE_SOURCE_DIR}/rust/async.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_SOURCE_DIR}/rust/async.rs" "${CMAKE_SOURCE_DIR}/include/monad/async/work_dispatcher.h"
    --allowlist-function "monad_async.*"
    --allowlist-type "monad_async.*"
    --block-extern-crate
    --generate-inline-functions
    --no-layout-tests
    DEPENDS
    "${CMAKE_SOURCE_DIR}/include/monad/async/context_switcher.h"
    "${CMAKE_SOURCE_DIR}/include/monad/async/executor.h"
    "${CMAKE_SOURCE_DIR}/include/monad/async/task.h"
    "${CMAKE_SOURCE_DIR}/include/monad/async/work_dispatcher.h"
  )
  add_custom_target(monad_async_regenerate_rust_bindings DEPENDS "${CMAKE_SOURCE_DIR}/rust/async.rs")
  add_dependencies(monad_async monad_async_regenerate_rust_bindings)
else()
  message(WARNING "WARNING: Could not regen Rust bindings as bindgen program not found")
endif()

enable_testing()

function(monad_test target)
  add_executable(${target} ${ARGN})
  target_link_libraries(${target} PRIVATE monad_async GTest::GTest GTest::Main)
  add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>)
endfunction()

monad_test(monad_async_executor_test "test/async/executor.cpp")

monad_test(monad_async_work_dispatcher_test "test/async/work_dispatcher.cpp")
