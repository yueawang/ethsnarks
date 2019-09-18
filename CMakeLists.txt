cmake_minimum_required(VERSION 2.8)
set(CMAKE_LEGACY_CYGWIN_WIN32 0)

project(ethsnarks)

if (CMAKE_VERSION VERSION_GREATER_EQUAL "3.13")
  cmake_policy(SET CMP0077 NEW) # ENABLE CMP0077: option() honors normal variables
endif()

if (CMAKE_VERSION VERSION_GREATER_EQUAL "3.9")
  cmake_policy(SET CMP0069 NEW) # Enable IPO for compilers other than only Intel C++ on Linux
endif()

option(ETHSNARKS_DISABLE_TESTS "Disable ethsnarks tests" OFF)
option(ETHSNARKS_DISABLE_UTILS "Disable ethsnarks utilties" ON)
option(ETHSNARKS_DISABLE_PINOCCHIO "Disable pinocchio / xjsnark compatibility" OFF)

option(ETHSNARKS_NO_THREADS "Disable testing for threads support" OFF)
if( NOT ${ETHSNARKS_NO_THREADS} )
  find_package(Threads REQUIRED)
endif()

if (CMAKE_VERSION VERSION_GREATER "3.0")
  set(CMAKE_CXX_STANDARD 11)
  set(CMAKE_CXX_STANDARD_REQUIRED ON) #...is required...
else()
  include(CheckCXXCompilerFlag)
  CHECK_CXX_COMPILER_FLAG("-std=c++11" COMPILER_SUPPORTS_CXX11)

  if(COMPILER_SUPPORTS_CXX11)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
  elseif(COMPILER_SUPPORTS_CXX0X)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
  else()
        message(STATUS "The compiler ${CMAKE_CXX_COMPILER} has no C++11 support. Please use a different C++ compiler.")
  endif()
endif()

if( NOT ${ETHSNARKS_DISABLE_TESTS} )
  include(CTest)
  enable_testing()
endif()

set(SHA3_USE_KECCAK ON)
add_definitions(-DSHA3_USE_KECCAK=1)

set(
  CURVE
  "ALT_BN128"
  CACHE
  STRING
  "Default curve: one of ALT_BN128, BN128, EDWARDS, MNT4, MNT6"
)

set(
  DEPENDS_DIR
  "${CMAKE_CURRENT_SOURCE_DIR}/depends"
  CACHE
  STRING
  "Optionally specify the dependency installation directory relative to the source directory (default: inside dependency folder)"
)

set(
  DEPENDS_DIR_LIBSNARK
  "${CMAKE_CURRENT_SOURCE_DIR}/depends/libsnark/"
  CACHE
  STRING
  "Optionally specify the dependency installation directory relative to the source directory (default: inside dependency folder)"
)

set(
  DEPENDS_DIR_LIBFF
  "${DEPENDS_DIR_LIBSNARK}/depends/libff/"
  CACHE
  STRING
  "Optionally specify the dependency installation directory relative to the source directory (default: inside dependency folder)"
)

set(
  DEPENDS_DIR_LIBFQFFT
  "${DEPENDS_DIR}/libfqfft/"
  CACHE
  STRING
  "Optionally specify the dependency installation directory relative to the source directory (default: inside dependency folder)"
)

set(
  OPT_FLAGS
  ""
  CACHE
  STRING
  "Override C++ compiler optimization flags"
)

option(
  USE_ASAN
  "Enable address sanitization, https://github.com/google/sanitizers"
  OFF
)

option(
  MULTICORE
  "Enable parallelized execution, using OpenMP"
  OFF
)

option(
  USE_MIXED_ADDITION
  "Convert each element of the key pair to affine coordinates"
  OFF
)

option(
  BINARY_OUTPUT
  "Use binary output for serialisation"
  ON
)

option(
  MONTGOMERY_OUTPUT
  "Serialize Fp elements as their Montgomery representations (faster but not human-readable)"
  ON
)

option(
  USE_ASM
  "Use architecture-specific optimized assembly code"
  ON
)


option(
  PERFORMANCE
  "Enable link-time and aggressive optimizations"
  OFF
)

option(
  WITH_PROCPS
  "Use procps for memory profiling"
  OFF
)

option(
  DEBUG
  "Enable debugging mode"
  OFF
)

option(
  CPPDEBUG
  "Enable debugging of C++ STL (does not imply DEBUG)"
  OFF
)


add_definitions(-DCURVE_${CURVE})

if(CMAKE_COMPILER_IS_GNUCXX OR "${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
  add_compile_options(-fPIC)
endif()

if(${CURVE} STREQUAL "BN128")
  add_definitions(-DBN_SUPPORT_SNARK=1)
endif()

if("${MULTICORE}")
  find_package(OpenMP REQUIRED)
  add_definitions(-DMULTICORE=1)
endif()

if("${USE_ASM}")
  add_definitions(-DUSE_ASM)
endif()

if("${BINARY_OUTPUT}")
  add_definitions(-DBINARY_OUTPUT)
endif()

if("${MONTGOMERY_OUTPUT}")
  add_definitions(-DMONTGOMERY_OUTPUT)
endif()

if(NOT "${USE_PT_COMPRESSION}")
  add_definitions(-DNO_PT_COMPRESSION=1)
endif()

if("${PERFORMANCE}")
  include(CheckIPOSupported)
  check_ipo_supported()
  set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

if("${USE_MIXED_ADDITION}")
  add_definitions(-DUSE_MIXED_ADDITION=1)
endif()

if("${CPPDEBUG}")
  add_definitions(-D_GLIBCXX_DEBUG -D_GLIBCXX_DEBUG_PEDANTIC)
endif()

include(FindPkgConfig)
if("${WITH_PROCPS}")
  pkg_check_modules(
    PROCPS
    REQUIRED

    libprocps
  )
else()
  add_definitions(
    -DNO_PROCPS
  )
endif()

if(CMAKE_COMPILER_IS_GNUCXX OR "${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
  # Common compilation flags and warning configuration
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wno-unused-variable")
endif()

if("${USE_ASAN}")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address")
endif()


# Locate the gmp library and its includes
find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_library(GMP_LIBRARY gmp)
if(GMP_LIBRARY MATCHES ${CMAKE_SHARED_LIBRARY_SUFFIX})
  set(gmp_library_type SHARED)
else()
  set(gmp_library_type STATIC)
endif()
message(STATUS "GMP: ${GMP_LIBRARY}, ${GMP_INCLUDE_DIR}")
add_library(gmp ${gmp_library_type} IMPORTED)
set_target_properties(
  gmp PROPERTIES
  IMPORTED_LOCATION ${GMP_LIBRARY}
  INTERFACE_INCLUDE_DIRECTORIES ${GMP_INCLUDE_DIR}
)


set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OPT_FLAGS}")

include(FindPkgConfig)
if("${WITH_PROCPS}")
  pkg_check_modules(PROCPS REQUIRED libprocps)
else()
  add_definitions(-DNO_PROCPS)
endif()


add_library(
  ff
  STATIC

  ${DEPENDS_DIR_LIBFF}/libff/algebra/curves/alt_bn128/alt_bn128_g1.cpp
  ${DEPENDS_DIR_LIBFF}/libff/algebra/curves/alt_bn128/alt_bn128_g2.cpp
  ${DEPENDS_DIR_LIBFF}/libff/algebra/curves/alt_bn128/alt_bn128_init.cpp
  ${DEPENDS_DIR_LIBFF}/libff/algebra/curves/alt_bn128/alt_bn128_pairing.cpp
  ${DEPENDS_DIR_LIBFF}/libff/algebra/curves/alt_bn128/alt_bn128_pp.cpp
  ${DEPENDS_DIR_LIBFF}/libff/common/double.cpp
  ${DEPENDS_DIR_LIBFF}/libff/common/profiling.cpp
  ${DEPENDS_DIR_LIBFF}/libff/common/utils.cpp
)

target_include_directories(ff PUBLIC
  ${GMP_INCLUDE_DIR}
  ${DEPENDS_DIR_LIBSNARK} ${DEPENDS_DIR_LIBFF} ${DEPENDS_DIR_LIBFQFFT})

set_property(TARGET ff PROPERTY CXX_STANDARD 11)


if("${DEBUG}" OR "${CMAKE_BUILD_TYPE}" STREQUAL "Debug")
  add_definitions(-DDEBUG=1)
  target_compile_definitions(ff PUBLIC DEBUG=1)
endif()

target_include_directories(ff INTERFACE
  ${GMP_INCLUDE_DIR}
  ${DEPENDS_DIR_LIBSNARK} ${DEPENDS_DIR_LIBFF} ${DEPENDS_DIR_LIBFQFFT})


target_link_libraries(ff ${GMP_LIBRARY} ${PROCPS_LIBRARIES})

if(OpenMP_CXX_FOUND)
    target_link_libraries(ff OpenMP::OpenMP_CXX)
endif()

add_subdirectory(src)
add_subdirectory(depends)
