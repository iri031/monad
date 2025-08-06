cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)

project(monad_storage)

add_library(
  monad_storage STATIC
  "config.hpp"
  "db_storage.cpp"
  "db_storage.hpp"
  "detail/db_metadata.hpp"
  "detail/unsigned_20.hpp"
  "detail/scope_polyfill.hpp"
  "util.cpp"
  "util.hpp"
)

target_include_directories(monad_storage PUBLIC ${CATEGORY_MAIN_DIR})
monad_compile_options(monad_storage)
target_link_libraries(monad_storage PUBLIC monad_core)

function(add_storage_test)
  set(ONE_VALUE_ARGS TARGET TEST_FILTER)
  set(MULTI_VALUE_ARGS SOURCES LINK_LIBRARIES)
  cmake_parse_arguments(ADD_TRIE_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(${ADD_TRIE_TEST_TARGET} ${ADD_TRIE_TEST_SOURCES})
  monad_compile_options(${ADD_TRIE_TEST_TARGET})
  target_link_libraries(
    ${ADD_TRIE_TEST_TARGET} PUBLIC monad_storage GTest::gtest_main
                                   ${ADD_TRIE_TEST_LINK_LIBRARIES})
  gtest_discover_tests(
    ${ADD_TRIE_TEST_TARGET}
    TEST_PREFIX ${PROJECT_NAME}/ TEST_FILTER ${ADD_TRIE_TEST_TEST_FILTER}
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

add_subdirectory("test")