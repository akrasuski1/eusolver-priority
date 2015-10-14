cmake_minimum_required(VERSION 3.2.0)
project(libeusolver)

set(CMAKE_CXX_FLAGS_RELEASE
  "-pipe -Wall -pedantic -flto -fPIC -std=c++14 -O3"
  CACHE STRING "C++ compiler flags for release build" FORCE)

set(CMAKE_C_FLAGS_RELEASE
  "-pipe -Wall -pedantic -std=c11 -flto -fPIC -O3"
  CACHE STRING "C compiler flags for release build" FORCE)

set(CMAKE_CXX_FLAGS_RELEASENOLTO
  "-pipe -Wall -pedantic -fPIC -std=c++14 -O3"
  CACHE STRING "C++ compiler flags for release build" FORCE)

set(CMAKE_C_FLAGS_RELEASENOLTO
  "-pipe -Wall -pedantic -std=c11 -fPIC -O3"
  CACHE STRING "C compiler flags for release build" FORCE)

set(CMAKE_CXX_FLAGS_DEBUG
  "-pipe -Wall -pedantic -ggdb3 -fno-inline -O0 -fPIC -std=c++14"
  CACHE STRING "C++ compiler flags for debug build" FORCE)

set(CMAKE_CXX_FLAGS_DEBUG
  "-pipe -Wall -pedantic -ggdb3 -fno-inline -O0 -fPIC -std=c11"
  CACHE STRING "C compiler flags for debug build" FORCE)

set(LIBEUSOLVER_CXX_SOURCE_FILES
  src/BitSet.cpp
  src/BitSetCAPI.cpp
  src/DecisionTree.cpp
  src/MultiLabelDecisionTreeLearner.cpp
  )

set(LIBEUSOLVER_C_SOURCE_FILES
  )

add_library(eusolver
  SHARED
  ${LIBEUSOLVER_CXX_SOURCE_FILES}
  ${LIBEUSOLVER_C_SOURCE_FILES}
  )

add_custom_command(TARGET eusolver
  POST_BUILD
  COMMAND cp ${CMAKE_CURRENT_SOURCE_DIR}/src/python/*.py ${CMAKE_BINARY_DIR}
  COMMAND python3 -m py_compile *.py
  )

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release
    CACHE STRING "Build Type: One of Release, ReleaseNOLTO, Debug" FORCE)
endif()
