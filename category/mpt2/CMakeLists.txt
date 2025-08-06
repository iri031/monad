cmake_minimum_required(VERSION 3.27)

include(CheckCXXSourceRuns)

project(monad_trie2)
enable_testing()

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# ##############################################################################
# deps
# ##############################################################################

find_package(Boost 1.83 # 1.83 really is the minimum
             CONFIG REQUIRED COMPONENTS context fiber json thread)
find_package(GTest)
find_package(PkgConfig REQUIRED)

add_library(
  monad_trie STATIC
  "config.hpp"
  "nibbles_view.hpp"
  "nibbles_view_fmt.hpp"
  "node.cpp"
  "node.hpp"
  "node_cursor.hpp"
  "ondisk_db_config.hpp"
  "request.hpp"
  "state_machine.hpp"
  "trie.cpp"
  "trie.hpp"
  "update.hpp"
  "update_aux.cpp"
  "util.hpp")

target_include_directories(monad_trie2 PUBLIC ${CATEGORY_MAIN_DIR})
target_include_directories(monad_trie2 PRIVATE "third_party")
monad_compile_options(monad_trie2)
target_link_libraries(monad_trie2 PRIVATE Boost::boost)
target_link_libraries(monad_trie2 PUBLIC concurrentqueue)