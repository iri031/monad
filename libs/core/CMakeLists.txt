cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)
include(CheckCXXSymbolExists)

project(monad_core LANGUAGES C CXX ASM)

if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(_monad_spinlock_track_owner_info ON)
  set(_monad_spinlock_track_stats ON)
else()
  set(_monad_spinlock_track_owner_info OFF)
  set(_monad_spinlock_track_stats OFF)
endif()

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(MONAD_CORE_SPINLOCK_TRACK_OWNER_INFO
       "enable source location of owner in spinlocks"
       ${_monad_spinlock_track_owner_info})
option(MONAD_CORE_SPINLOCK_TRACK_STATS
       "enable contention statistics tracking of spinlocks"
       ${_monad_spinlock_track_stats})
option(MONAD_CORE_SPINLOCK_TRACK_STATS_ATOMIC
       "use fetch_add on atomics statistics tracking" OFF)

# ##############################################################################
# deps
# ##############################################################################

include("cmake/find_our_dependency.cmake")

cmake_host_system_information(RESULT linux_flavour QUERY DISTRIB_ID)
if(linux_flavour MATCHES "debian|ubuntu")
  find_package(Boost REQUIRED COMPONENTS stacktrace_backtrace)
else()
  find_package(Boost REQUIRED COMPONENTS stacktrace_addr2line)
endif()

find_package(TBB REQUIRED)


add_subdirectory("third_party/monad-boost-context")

add_subdirectory("third_party/nanobench")

add_subdirectory("third_party/nlohmann_json" SYSTEM)

add_subdirectory("third_party/unordered_dense")

add_subdirectory("third_party/quill" SYSTEM)

add_library(
  openssl_sha3_asm INTERFACE
  "third_party/openssl/crypto/sha/asm/keccak1600-avx2.S"
  "third_party/openssl/crypto/sha/asm/keccak1600-avx512.S")
target_include_directories(openssl_sha3_asm INTERFACE "third_party/openssl")

# ##############################################################################
# libs
# ##############################################################################

add_library(monad_core_c OBJECT
  "src/monad/core/dump.h"
  "src/monad/core/dump.c"
  "src/monad/core/spinlock.h"
  "src/monad/core/srcloc.h"
  "src/monad/fiber/fiber.h"
  "src/monad/fiber/fiber.c"
  "src/monad/fiber/fiber_thr.c"
  "src/monad/fiber/fiber_util.h"
  "src/monad/fiber/fiber_util.c"
  "src/monad/fiber/fiber_sync.h"
  "src/monad/fiber/fiber_channel.h"
  "src/monad/fiber/fiber_semaphore.h"
  "src/monad/fiber/run_queue.h"
  "src/monad/fiber/run_queue.c")

if (MONAD_CORE_SPINLOCK_TRACK_OWNER_INFO)
  target_compile_definitions(monad_core_c
          PUBLIC MONAD_SPINLOCK_TRACK_OWNER_INFO)
endif()

if (MONAD_CORE_SPINLOCK_TRACK_STATS)
  target_compile_definitions(monad_core_c
          PUBLIC MONAD_SPINLOCK_TRACK_STATS)
endif()

if (MONAD_CORE_SPINLOCK_TRACK_STATS_ATOMIC)
  target_compile_definitions(monad_core_c
          PUBLIC MONAD_SPINLOCK_TRACK_STATS_ATOMIC)
endif()

target_compile_features(monad_core_c PRIVATE c_std_23)
target_compile_options(monad_core_c PRIVATE -Wall -Werror -Wextra)

target_include_directories(monad_core_c
        PUBLIC "${PROJECT_SOURCE_DIR}/src")
target_link_libraries(monad_core_c PRIVATE monad_boost_context)

# XXX fix this later
target_include_directories(monad_core_c PRIVATE /usr/include/libunwind)
target_link_libraries(monad_core_c PRIVATE unwind)

add_library(
  monad_core STATIC
  # config
  "src/monad/config.hpp"
  # core
  "src/monad/core/array.hpp"
  "src/monad/core/assert.c"
  "src/monad/core/assert.h"
  "src/monad/core/backtrace.cpp"
  "src/monad/core/backtrace.hpp"
  "src/monad/core/basic_formatter.hpp"
  "src/monad/core/bit_util.h"
  "src/monad/core/byte_string.hpp"
  "src/monad/core/bytes_hash_compare.hpp"
  "src/monad/core/cmemory.hpp"
  "src/monad/core/cgroup.c"
  "src/monad/core/cgroup.h"
  "src/monad/core/cleanup.h"
  "src/monad/core/cleanup.c"
  "src/monad/core/cpuset.c"
  "src/monad/core/cpuset.h"
  "src/monad/core/cpu_relax.h"
  "src/monad/core/dump.hpp"
  "src/monad/core/endian.hpp"
  "src/monad/core/hash.hpp"
  "src/monad/core/hex_literal.hpp"
  "src/monad/core/keccak.c"
  "src/monad/core/keccak.h"
  "src/monad/core/keccak.hpp"
  "src/monad/core/keccak_impl.S"
  "src/monad/core/likely.h"
  "src/monad/core/math.hpp"
  "src/monad/core/nibble.h"
  "src/monad/core/offset.hpp"
  "src/monad/core/result.hpp"
  "src/monad/core/size_of.hpp"
  "src/monad/core/small_prng.hpp"
  "src/monad/core/tl_tid.c"
  "src/monad/core/tl_tid.h"
  "src/monad/core/unaligned.hpp"
  "src/monad/lru/lru_cache.hpp"
  "src/monad/lru/static_lru_cache.hpp"
  "src/monad/mem/batch_mem_pool.hpp"
  "src/monad/synchronization/spin_lock.hpp"
  # fiber
  "src/monad/fiber/config.hpp"
  "src/monad/fiber/future.hpp"
  "src/monad/fiber/priority_pool.cpp"
  "src/monad/fiber/priority_pool.hpp"
  "src/monad/fiber/priority_task.hpp"
  # io
  "src/monad/io/buffer_pool.cpp"
  "src/monad/io/buffer_pool.hpp"
  "src/monad/io/buffers.cpp"
  "src/monad/io/buffers.hpp"
  "src/monad/io/config.hpp"
  "src/monad/io/ring.cpp"
  "src/monad/io/ring.hpp"
  # mem
  "src/monad/mem/cpool.h"
  "src/monad/mem/dynamic_allocator.hpp"
  "src/monad/mem/huge_mem.c"
  "src/monad/mem/huge_mem.cpp"
  "src/monad/mem/huge_mem.h"
  "src/monad/mem/huge_mem.hpp"
  "src/monad/mem/mem_map.cpp"
  "src/monad/mem/mem_map.hpp"
  # procfs
  "src/monad/procfs/statm.c"
  "src/monad/procfs/statm.h"
  # rlp
  "src/monad/rlp/config.hpp"
  "src/monad/rlp/encode.hpp"
  # test
  "src/monad/test/gtest_signal_stacktrace_printer.hpp"
  # util
  "src/monad/util/stopwatch.hpp")
target_include_directories(monad_core PUBLIC "src")
monad_compile_options(monad_core)
target_compile_definitions(monad_core PUBLIC "BOOST_STACKTRACE_LINK=1")
target_compile_definitions(monad_core PUBLIC "_GNU_SOURCE")
if(linux_flavour MATCHES "debian|ubuntu")
  target_compile_definitions(monad_core
                             PUBLIC "BOOST_STACKTRACE_USE_BACKTRACE=1")
  target_link_libraries(monad_core PUBLIC Boost::stacktrace_backtrace)
else()
  target_compile_definitions(monad_core
                             PUBLIC "BOOST_STACKTRACE_USE_ADDR2LINE=1")
  target_link_libraries(monad_core PUBLIC Boost::stacktrace_addr2line)
endif()
target_link_libraries(monad_core PUBLIC cgroup openssl_sha3_asm uring TBB::tbb)
target_link_libraries(monad_core PUBLIC komihash)
target_link_libraries(monad_core PUBLIC ethash::keccak)
target_link_libraries(monad_core PUBLIC evmc)
target_link_libraries(monad_core PRIVATE monad_core_c)

add_library(
  monad_core_disas STATIC
  # core
  "src/monad/core/math_disas.cpp"
  "src/monad/core/offset_disas.cpp"
  "src/monad/core/spinlock_disas.c"
  "src/monad/mem/cpool_disas.c"
  # rlp
  "src/monad/rlp/encode_disas.cpp")
monad_compile_options(monad_core_disas)
target_link_libraries(monad_core_disas PUBLIC monad_core)

# ##############################################################################
# tests
# ##############################################################################

enable_testing()

find_package(GTest REQUIRED)

add_subdirectory("test")

monad_add_test(bit_util_test src/monad/core/bit_util_test.cpp)
monad_add_test(huge_mem_test src/monad/mem/huge_mem_test.cpp)
monad_add_test(static_lru_test src/monad/lru/static_lru_test.cpp)
