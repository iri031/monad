cmake_minimum_required(VERSION 3.5)

project(new-executor LANGUAGES C CXX)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)

add_subdirectory("third_party/boost-context")

set(monad_async_INCLUDES
  "include/monad/async/context_switcher.h"
  "include/monad/async/executor.h"
  "include/monad/async/file_io.h"
  "include/monad/async/task.h"
  "include/monad/async/util.h"
  "include/monad/async/work_dispatcher.h"
)
add_library(monad_async STATIC
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
target_link_libraries(monad_async PUBLIC uring Boost::boost)

add_library(monad_fiber STATIC
  "src/monad/fiber/scheduler.c"
  "src/monad/fiber/context.c"
  "src/monad/fiber/current.c"
  "src/monad/fiber/task.c"
  "src/monad/fiber/channel.c"
)
target_compile_features(monad_fiber PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_fiber PUBLIC -Wall -Wextra -Wconversion -Wpedantic)
target_include_directories(monad_fiber PUBLIC "include")
target_link_libraries(monad_fiber PUBLIC Boost::context)

if(BINDGEN_PROGRAM)
  make_directory("${CMAKE_SOURCE_DIR}/rust")
  add_custom_command(OUTPUT "${CMAKE_SOURCE_DIR}/rust/async.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_SOURCE_DIR}/rust/async.rs"
    "${CMAKE_SOURCE_DIR}/include/monad/async/all.h"
    --allowlist-function "monad_async.*"
    --allowlist-type "monad_async.*"
    --block-extern-crate
    --generate-inline-functions
    --no-layout-tests
    DEPENDS ${monad_async_INCLUDES}
  )
  add_custom_command(OUTPUT "${CMAKE_SOURCE_DIR}/rust/fiber.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_SOURCE_DIR}/rust/fiber.rs"
    "${CMAKE_SOURCE_DIR}/include/monad/fiber/all.h"
    --allowlist-function "monad_fiber.*"
    --allowlist-type "monad_fiber.*"
    --block-extern-crate
    --generate-inline-functions
    --no-layout-tests
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
