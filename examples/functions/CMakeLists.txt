cmake_minimum_required(VERSION 3.25)
set(CMAKE_CXX_STANDARD 23)
add_executable(ex_functions
    functions.cpp)

refl_config(ex_functions)
target_compile_options(ex_functions PRIVATE
    $<$<OR:$<CXX_COMPILER_ID:Clang>>:
        -Weverything
        -Wno-c++98-compat -Wno-c++98-compat-pedantic -Wno-pre-c++17-compat -Wno-pre-c++20-compat -Wno-c++20-compat
        -Wno-covered-switch-default -Wno-unknown-attributes -Wno-padded
>)
