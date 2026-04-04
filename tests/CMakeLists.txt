cmake_minimum_required(VERSION 3.25)
set(CMAKE_CXX_STANDARD 23)

include(FetchContent)
FetchContent_Declare(
  Catch2
  GIT_SHALLOW    TRUE
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG        v3.8.1
  SYSTEM)
FetchContent_MakeAvailable(Catch2)

list(APPEND CMAKE_MODULE_PATH ${Catch2_SOURCE_DIR}/extras)

add_executable(tests
    test_class.cpp
    test_enum.cpp)

refl_config(tests)
target_link_libraries(tests PRIVATE Catch2::Catch2WithMain)
target_compile_options(tests PRIVATE
    $<$<OR:$<CXX_COMPILER_ID:Clang>>:
        -Weverything
        -Wno-c++98-compat -Wno-c++98-compat-pedantic -Wno-pre-c++17-compat -Wno-pre-c++20-compat -Wno-c++20-compat
        -Wno-covered-switch-default -Wno-unknown-attributes
>)

include(CTest)
include(Catch)
catch_discover_tests(tests)
