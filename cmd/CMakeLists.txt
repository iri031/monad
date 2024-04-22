include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(CLI11 REQUIRED)

add_executable(replay_ethereum replay_ethereum.cpp)
monad_compile_options(replay_ethereum)

target_link_libraries(replay_ethereum PRIVATE monad CLI11::CLI11)

add_executable(test_run_loop test_run_loop.cpp)
monad_compile_options(test_run_loop)

target_link_libraries(test_run_loop PRIVATE monad CLI11::CLI11)
