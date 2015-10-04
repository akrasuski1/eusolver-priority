cmake_minimum_required(VERSION 3.2.0)
project(libeusolver)

set(CMAKE_CXX_FLAGS_RELEASE
  "-Wall -pedantic -flto -fPIC -std=c++14 -O3"
  CACHE STRING "C++ compiler flags for release build" FORCE)

set(CMAKE_C_FLAGS_RELEASE
  "-Wall -pedantic -std=c11 -flto -fPIC -O3"
  CACHE STRING "C compiler flags for release build" FORCE)

set(CMAKE_CXX_FLAGS_DEBUG
  "-Wall -pedantic -ggdb3 -fno-inline -O0 -fPIC -std=c++14"
  CACHE STRING "C++ compiler flags for debug build" FORCE)

set(CMAKE_CXX_FLAGS_DEBUG
  "-Wall -pedantic -ggdb3 -fno-inline -O0 -fPIC -std=c11"
  CACHE STRING "C compiler flags for debug build" FORCE)

set(LIBEUSOLVER_CXX_SOURCE_FILES
  src/BitSet.cpp
  )

set(LIBEUSOLVER_C_SOURCE_FILES
  )

add_library(eusolver
  SHARED
  ${LIBEUSOLVER_CXX_SOURCE_FILES}
  ${LIBEUSOLVER_C_SOURCE_FILES}
  )

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release
    CACHE STRING "Build Type: One of Release, ReleaseLTO, Debug" FORCE)
endif()
