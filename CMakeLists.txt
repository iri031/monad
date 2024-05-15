cmake_minimum_required(VERSION 3.5)

project(new-executor LANGUAGES C CXX)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)
find_program(RUSTC_PROGRAM rustc)

add_subdirectory("third_party/boost-context")

add_library(monad_fiber STATIC
  "src/monad/fiber/scheduler.c"
  "src/monad/fiber/context.c"
  "src/monad/fiber/current.c"
  "src/monad/fiber/current_thread_local.c"
  "src/monad/fiber/task.c"
  "src/monad/fiber/channel.c"
  "src/monad/fiber/pool.c"
)
target_compile_features(monad_fiber PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_fiber PUBLIC -Wall -Wextra -Wconversion -Wpedantic)
target_include_directories(monad_fiber PUBLIC "include")
target_link_libraries(monad_fiber PUBLIC Boost::context)

set(monad_async_INCLUDES
  "include/monad/async/context_switcher.h"
  "include/monad/async/executor.h"
  "include/monad/async/file_io.h"
  "include/monad/async/task.h"
  "include/monad/async/util.h"
  "include/monad/async/work_dispatcher.h"
)
add_library(monad_async STATIC
  "src/monad/async/context_switcher_monad_fiber.c"
  "src/monad/async/context_switcher_none.c"
  "src/monad/async/context_switcher_sjlj.c"
  "src/monad/async/executor.c"
  "src/monad/async/file_io.c"
  "src/monad/async/result.cpp"
  "src/monad/async/task.c"
  "src/monad/async/util.cpp"
  "src/monad/async/work_dispatcher.c"
)
target_compile_features(monad_async PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_async PUBLIC -Wall -Wextra -Wconversion -Wpedantic)
target_include_directories(monad_async PUBLIC "include")
target_link_libraries(monad_async PUBLIC uring Boost::boost monad_fiber)

if(BINDGEN_PROGRAM)
  add_custom_command(OUTPUT "${CMAKE_SOURCE_DIR}/rust/async.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_SOURCE_DIR}/rust/async.rs"
    "${CMAKE_SOURCE_DIR}/include/monad/async/all.h"
    --allowlist-function "monad_async.*"
    --allowlist-type "monad_async.*"
    --allowlist-var "monad_async.*"
    --generate-inline-functions
    --no-layout-tests
    --no-derive-copy
    --with-derive-default
#    --must-use-type cxx_result_status_code_system_monad_async
    DEPENDS ${monad_async_INCLUDES}
  )
  add_custom_command(OUTPUT "${CMAKE_SOURCE_DIR}/rust/fiber.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_SOURCE_DIR}/rust/fiber.rs"
    "${CMAKE_SOURCE_DIR}/include/monad/fiber/all.h"
    --allowlist-function "monad_fiber.*"
    --allowlist-type "monad_fiber.*"
    --allowlist-var "monad_fiber.*"
    --generate-inline-functions
    --no-layout-tests
    --no-derive-copy
    --with-derive-default
#    --must-use-type cxx_result_status_code_system_monad_async
    DEPENDS "${CMAKE_SOURCE_DIR}/include/monad/fiber/all.h"
  )
  add_custom_target(monad_async_regenerate_rust_bindings DEPENDS "${CMAKE_SOURCE_DIR}/rust/async.rs" "${CMAKE_SOURCE_DIR}/rust/fiber.rs")
  add_dependencies(monad_async monad_async_regenerate_rust_bindings)
  add_dependencies(monad_fiber monad_async_regenerate_rust_bindings)
else()
  message(WARNING "WARNING: Could not regen Rust bindings as bindgen program not found")
endif()

enable_testing()

add_subdirectory("test")

if(RUSTC_PROGRAM AND NOT CMAKE_C_FLAGS_INIT MATCHES "fsanitize=")
  add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/test/rust_tests"
    COMMAND "${RUSTC_PROGRAM}" --test -o "${CMAKE_BINARY_DIR}/test/rust_tests"
    "${CMAKE_SOURCE_DIR}/rust/test.rs"
    -L "$<TARGET_FILE_DIR:monad_async>"
    -l $<TARGET_NAME:monad_async>
    -l stdc++
    -l uring
    DEPENDS
      "${CMAKE_SOURCE_DIR}/rust/async_with_rust_helpers.rs"
      "${CMAKE_SOURCE_DIR}/rust/test.rs"
      "${CMAKE_SOURCE_DIR}/rust/async.rs"
      "${CMAKE_SOURCE_DIR}/rust/fiber.rs"
  )
  add_custom_target(monad_async_rust_tests ALL DEPENDS "${CMAKE_BINARY_DIR}/test/rust_tests")
  add_dependencies(monad_async_rust_tests monad_async monad_fiber)
  add_test(NAME monad_async_rust_tests COMMAND "${CMAKE_BINARY_DIR}/test/rust_tests" --nocapture)
endif()
