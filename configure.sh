CC=clang-18 CXX=clang++-18 cmake \
    -DCMAKE_TOOLCHAIN_FILE:STRING=libs/core/toolchains/gcc-avx2.cmake \
    -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
    -DCMAKE_BUILD_TYPE:STRING=RelWithDebInfo \
    -B build -G Ninja
