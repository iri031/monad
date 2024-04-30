cmake_minimum_required(VERSION 3.5)

project(new-executor LANGUAGES C CXX)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(GTest REQUIRED)
find_package(Boost REQUIRED COMPONENTS context)
find_program(BINDGEN_PROGRAM bindgen)

include(CheckCXXSourceRuns)
function(check_if_boost_fiber_needs_ucontext_macro)
  set(BOOST_CONTEXT_WAS_COMPILED_WITH_UCONTEXT FALSE PARENT_SCOPE)
  set(prog "#include <boost/context/fiber.hpp>\nint main(void){\n::boost::context::fiber foo;\nreturn 0;\n}")
  set(CMAKE_REQUIRED_LIBRARIES "Boost::context")
  check_cxx_source_runs("${prog}" BOOST_FIBER_LINKS_WITHOUT_ADDITIONAL_MACROS)
  if(NOT BOOST_FIBER_LINKS_WITHOUT_ADDITIONAL_MACROS)
    set(CMAKE_REQUIRED_DEFINITIONS "-DBOOST_USE_UCONTEXT=1")
    check_cxx_source_runs("${prog}" BOOST_FIBER_LINKS_WITH_BOOST_USE_UCONTEXT_MACRO)
    if(BOOST_FIBER_LINKS_WITH_BOOST_USE_UCONTEXT_MACRO)
      get_target_property(var Boost::context INTERFACE_COMPILE_DEFINITIONS)
      list(APPEND var "-DBOOST_USE_UCONTEXT=1")
      set_target_properties(Boost::context PROPERTIES INTERFACE_COMPILE_DEFINITIONS "${var}")
      set(BOOST_CONTEXT_WAS_COMPILED_WITH_UCONTEXT TRUE PARENT_SCOPE)
    else()
      message(FATAL_ERROR "FATAL: Boost.Context needs additional help to link, and I need to be taught what")
    endif()
  endif()
endfunction()
check_if_boost_fiber_needs_ucontext_macro()

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

if(NOT BOOST_CONTEXT_WAS_COMPILED_WITH_UCONTEXT)
  add_library(monad_fiber STATIC
    "src/monad/fiber/scheduler.c"
    "src/monad/fiber/context.c"
    "src/monad/fiber/current.c"
    "src/monad/fiber/task.c"
  )
  target_compile_features(monad_fiber PUBLIC c_std_23 cxx_std_20)
  target_compile_options(monad_fiber PUBLIC -Wall -Wextra -Wconversion -Wpedantic)
  target_include_directories(monad_fiber PUBLIC "include")
  target_link_libraries(monad_fiber PUBLIC Boost::context)
endif()

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

add_subdirectory("test")
