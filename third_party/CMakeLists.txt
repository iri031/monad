find_program(CARGO_PROGRAM cargo)

if(CARGO_PROGRAM AND NOT CMAKE_C_FLAGS_INIT MATCHES "fsanitize=")
  set(target "${CMAKE_BINARY_DIR}/libs/runloop/src/monad/async/category-mio/libmio.rlib2")
  cmake_host_system_information(RESULT linux_flavour QUERY DISTRIB_ID)
  if(linux_flavour MATCHES "debian|ubuntu")
      find_package(Boost REQUIRED stacktrace_backtrace)
      add_library(boost_stacktrace_backtrace ALIAS Boost::stacktrace_backtrace)
      set(BOOST_STACKTRACE_LIB boost_stacktrace_backtrace)
  else()
      find_package(Boost REQUIRED stacktrace_addr2line)
      add_library(boost_stacktrace_addr2line ALIAS Boost::stacktrace_addr2line)
      set(BOOST_STACKTRACE_LIB boost_stacktrace_addr2line)
  endif()
  set(rustflags --cfg mio_monad_async
    -L "$<TARGET_FILE_DIR:monad_async_c>"
    -L "$<TARGET_FILE_DIR:monad_context_c>"
    -L "$<TARGET_FILE_DIR:monad_core>"
    -l $<TARGET_NAME:monad_async_c>
    -l $<TARGET_NAME:monad_context_c>
    -l $<TARGET_NAME:monad_core>
    -L "$<TARGET_FILE_DIR:${BOOST_STACKTRACE_LIB}>"
    -l $<TARGET_NAME:${BOOST_STACKTRACE_LIB}>
    -l stdc++
    -l uring
  )
  string(REPLACE ";" " " rustflags "${rustflags}")
  add_custom_command(OUTPUT "${target}"
#    COMMAND "CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/category-mio" "${CARGO_PROGRAM}" build --all-targets
    COMMAND "CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/libs/runloop/src/monad/async/category-mio" "RUSTFLAGS=${rustflags}" "${CARGO_PROGRAM}" build --all-targets --all-features
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/third_party/category-mio"
  )
  add_custom_target(category_mio_rust_tests ALL DEPENDS "${target}")
  add_dependencies(category_mio_rust_tests monad_async_c monad_context_c)
  add_test(NAME category-mio-rust-tests
    COMMAND "${CARGO_PROGRAM}" test --all-targets --all-features
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/third_party/category-mio"
  )
  set_tests_properties(category-mio-rust-tests PROPERTIES
    ENVIRONMENT "CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/libs/runloop/src/monad/async/category-mio"
    ENVIRONMENT "RUSTFLAGS=${rustflags}")
endif()
