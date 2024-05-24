cmake_minimum_required(VERSION 3.5)

project(monad-runloop LANGUAGES C CXX)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)
find_program(RUSTC_PROGRAM rustc)

add_subdirectory("third_party/boost-context")

add_library(monad_fiber_c STATIC
  "src/monad/fiber/scheduler.c"
  "src/monad/fiber/context.c"
  "src/monad/fiber/context_thread_local.c"
  "src/monad/fiber/current.c"
  "src/monad/fiber/current_thread_local.c"
  "src/monad/fiber/task.c"
  "src/monad/fiber/channel.c"
  "src/monad/fiber/pool.c"
)
target_compile_features(monad_fiber_c PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_fiber_c PUBLIC -Wall -Wextra -Wconversion -Wpedantic -Werror)
target_include_directories(monad_fiber_c PUBLIC "src")
target_link_libraries(monad_fiber_c PUBLIC boost_context)

set(monad_async_INCLUDES
  "src/monad/async/context_switcher.h"
  "src/monad/async/executor.h"
  "src/monad/async/file_io.h"
  "src/monad/async/socket_io.h"
  "src/monad/async/task.h"
  "src/monad/async/util.h"
  "src/monad/async/work_dispatcher.h"
)
add_library(monad_async_c STATIC
  "src/monad/async/context_switcher_monad_fiber.c"
  "src/monad/async/context_switcher_none.c"
  "src/monad/async/context_switcher_sjlj.c"
  "src/monad/async/executor.c"
  "src/monad/async/file_io.c"
  "src/monad/async/result.cpp"
  "src/monad/async/socket_io.c"
  "src/monad/async/task.c"
  "src/monad/async/util.cpp"
  "src/monad/async/work_dispatcher.c"
)
target_compile_features(monad_async_c PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_async_c PUBLIC -Wall -Wextra -Wconversion -Wpedantic -Werror)
target_include_directories(monad_async_c PUBLIC "src")
target_link_libraries(monad_async_c PUBLIC uring Boost::boost monad_fiber_c)

if(BINDGEN_PROGRAM)
  add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/monad/async/all.h"
    --allowlist-function "monad_async.*"
    --allowlist-type "monad_async.*"
    --allowlist-var "monad_async.*"
    --generate-inline-functions
    --no-layout-tests
    --no-copy "monad_async.*"
    --with-derive-default
#    --must-use-type cxx_result_status_code_system_monad_async
    DEPENDS ${monad_async_INCLUDES}
  )
  add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/rust/fiber.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_CURRENT_SOURCE_DIR}/rust/fiber.rs"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/monad/fiber/all.h"
    --allowlist-function "monad_fiber.*"
    --allowlist-type "monad_fiber.*"
    --allowlist-var "monad_fiber.*"
    --generate-inline-functions
    --no-layout-tests
    --no-copy "monad_async.*"
    --with-derive-default
#    --must-use-type cxx_result_status_code_system_monad_async
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/src/monad/fiber/all.h"
  )
  add_custom_target(monad_async_c_regenerate_rust_bindings DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs" "${CMAKE_CURRENT_SOURCE_DIR}/rust/fiber.rs")
  add_dependencies(monad_async_c monad_async_c_regenerate_rust_bindings)
  add_dependencies(monad_fiber_c monad_async_c_regenerate_rust_bindings)
else()
  message(WARNING "WARNING: Could not regen Rust bindings as bindgen program not found")
endif()

enable_testing()

add_subdirectory("src/monad/async/test")
add_subdirectory("src/monad/fiber/test")

if(RUSTC_PROGRAM AND NOT CMAKE_C_FLAGS_INIT MATCHES "fsanitize=")
  add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/test/rust_tests"
    COMMAND "${RUSTC_PROGRAM}" --test -o "${CMAKE_BINARY_DIR}/test/rust_tests"
    "${CMAKE_CURRENT_SOURCE_DIR}/rust/test.rs"
    -L "$<TARGET_FILE_DIR:monad_async_c>"
    -l $<TARGET_NAME:monad_async_c>
    -l $<TARGET_NAME:monad_fiber_c>
    -L "$<TARGET_FILE_DIR:boost_context>"
    -l $<TARGET_NAME:boost_context>
    -l stdc++
    -l uring
    DEPENDS
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/async_with_rust_helpers.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/test.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/fiber.rs"
  )
  add_custom_target(monad_async_c_rust_tests ALL DEPENDS "${CMAKE_BINARY_DIR}/test/rust_tests")
  add_dependencies(monad_async_c_rust_tests monad_async_c monad_fiber_c)
  add_test(NAME monad_async_c_rust_tests COMMAND "${CMAKE_BINARY_DIR}/test/rust_tests" --nocapture)
endif()
