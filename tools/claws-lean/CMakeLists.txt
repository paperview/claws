find_package(Clang REQUIRED CONFIG)

add_executable(claws-lean main.cpp)
target_include_directories(claws-lean SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
target_compile_definitions(claws-lean PRIVATE ${LLVM_DEFINITIONS_LIST})
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(claws-lean PRIVATE -fno-rtti)
endif()
target_link_libraries(claws-lean PRIVATE clang-cpp LLVM)

# The tool drives this LLVM's clang, so it needs its header paths.
target_compile_definitions(claws-lean PRIVATE
  CLAWS_CLANG="${LLVM_TOOLS_BINARY_DIR}/clang++"
  CLAWS_RESOURCE_DIR="${LLVM_LIBRARY_DIR}/clang/${LLVM_VERSION_MAJOR}"
  CLAWS_SDK="${CLAWS_SDK}"
  CLAWS_INCLUDE_ROOT="${PROJECT_SOURCE_DIR}/include")
