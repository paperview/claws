cmake_minimum_required(VERSION 3.20)
project(claws C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# The tools drive the clang of the LLVM they link, which on macOS needs
# the SDK for the system headers.
set(CLAWS_SDK "")
if(APPLE)
  execute_process(COMMAND xcrun --show-sdk-path OUTPUT_VARIABLE CLAWS_SDK OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()

add_subdirectory(tools/claws-lean)
add_subdirectory(tools/claws-ast)
