cmake_minimum_required (VERSION 3.13)

project (xacc-voqc LANGUAGES C CXX)
enable_testing()

set (CMAKE_STANDARD_REQUIRED ON)
set (CMAKE_CXX_STANDARD 17)
set (CMAKE_EXPORT_COMPILE_COMMANDS TRUE)

if (NOT XACC_DIR)
  set(XACC_DIR "$ENV{HOME}/.xacc")
endif()

# Find Xacc
find_package(XACC REQUIRED)

# Build the VOQC plugin for XACC
add_subdirectory(xacc)