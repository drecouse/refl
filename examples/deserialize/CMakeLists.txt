cmake_minimum_required(VERSION 3.25)
set(CMAKE_CXX_STANDARD 23)
add_executable(ex_deserialize
    deserialize.cpp)
set(CLANG_DEFAULT_CXX_STDLIB "libc++")

refl_config(ex_deserialize)
target_compile_options(ex_deserialize PRIVATE
    $<$<OR:$<CXX_COMPILER_ID:Clang>>:
        -Weverything
        -Wno-c++98-compat -Wno-c++98-compat-pedantic -Wno-pre-c++17-compat -Wno-pre-c++20-compat -Wno-c++20-compat
        -Wno-covered-switch-default -Wno-unknown-attributes -Wno-unsafe-buffer-usage -Wno-unused-private-field
>)
