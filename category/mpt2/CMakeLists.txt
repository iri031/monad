cmake_minimum_required(VERSION 3.27)

include(CheckCXXSourceRuns)

project(monad_trie2)
enable_testing()

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# ##############################################################################
# deps
# ##############################################################################

# find_package(Boost 1.83 # 1.83 really is the minimum
#              CONFIG REQUIRED COMPONENTS context fiber json thread)
find_package(GTest)
find_package(PkgConfig REQUIRED)

add_library(
  monad_trie2 STATIC
  "child_data.cpp"
  "child_data.hpp"
  "compute.cpp"
  "compute.hpp"
  "config.hpp"
  "nibbles_view.hpp"
  "node.cpp"
  "node.hpp"
  "node_cursor.hpp"
  "request.hpp"
  "state_machine.hpp"
  "trie.cpp"
  "trie.hpp"
  "update.hpp"
  "update_aux.cpp"
  "util.hpp"
)

target_include_directories(monad_trie2 PUBLIC ${CATEGORY_MAIN_DIR})
target_include_directories(monad_trie2 PRIVATE "third_party")
monad_compile_options(monad_trie2)
target_link_libraries(monad_trie2 PUBLIC monad_storage)


function(add_mpt_test)
  set(ONE_VALUE_ARGS TARGET TEST_FILTER)
  set(MULTI_VALUE_ARGS SOURCES LINK_LIBRARIES)
  cmake_parse_arguments(ADD_TRIE_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(${ADD_TRIE_TEST_TARGET} ${ADD_TRIE_TEST_SOURCES})
  monad_compile_options(${ADD_TRIE_TEST_TARGET})
  target_link_libraries(
    ${ADD_TRIE_TEST_TARGET} PUBLIC monad_trie2 GTest::gtest_main
                                   ${ADD_TRIE_TEST_LINK_LIBRARIES})
  gtest_discover_tests(
    ${ADD_TRIE_TEST_TARGET}
    TEST_PREFIX ${PROJECT_NAME}/ TEST_FILTER ${ADD_TRIE_TEST_TEST_FILTER}
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

add_subdirectory("test")
