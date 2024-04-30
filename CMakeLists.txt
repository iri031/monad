cmake_minimum_required(VERSION 3.26)
project(fiber_sandbox)

set(CMAKE_CXX_STANDARD 20)

add_library(monad_fiber_sandbox src/scheduler.c src/context.c src/current.c src/task.c)

find_package(Boost REQUIRED context)

target_include_directories(monad_fiber_sandbox PUBLIC include)
target_link_libraries(monad_fiber_sandbox PUBLIC Boost::context)

add_subdirectory(test)