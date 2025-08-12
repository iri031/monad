cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_rpc)

option(MONAD_RPC_SHARED "Build monad_rpc shared, regardless of BUILD_SHARED_LIBS setting" OFF)

if (MONAD_RPC_SHARED)
  add_library(monad_rpc SHARED)
else()
  add_library(monad_rpc)
endif()

target_sources(monad_rpc PRIVATE "eth_call.cpp" "eth_call.h")
target_include_directories(monad_rpc PUBLIC ${CATEGORY_MAIN_DIR})

monad_compile_options(monad_rpc)
target_link_libraries(monad_rpc PRIVATE monad_execution)

monad_add_test_folder(".")
