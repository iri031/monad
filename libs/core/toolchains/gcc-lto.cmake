# This toolchain is good for a basic AVX512 CPU
set(CMAKE_ASM_FLAGS_INIT "-march=skylake-avx512")
set(CMAKE_C_FLAGS_INIT "-march=skylake-avx512 -flto -DMONAD_CONTEXT_PUBLIC_CONST=")
set(CMAKE_CXX_FLAGS_INIT "-march=skylake-avx512 -flto -DMONAD_CONTEXT_PUBLIC_CONST=")
set(CMAKE_EXE_LINKER_FLAGS_INIT "-flto -O2")
