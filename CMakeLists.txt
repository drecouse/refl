cmake_minimum_required(VERSION 3.25)
project(refl LANGUAGES CXX)
set(CMAKE_CXX_STANDARD 23)

option(REFL_BUILD_EXAMPLES "Build examples" OFF)
option(REFL_ENABLE_TESTING "Enable testing" OFF)

add_library(refl INTERFACE)
target_include_directories(refl INTERFACE
    "${CMAKE_CURRENT_SOURCE_DIR}/include")

find_package(LLVM)

add_library(refl-plugin MODULE
    src/attribute.cpp
    src/plugin.cpp)

target_compile_options(refl-plugin PRIVATE
    $<$<OR:$<CXX_COMPILER_ID:Clang>>:
        -Weverything
        -Wno-c++98-compat -Wno-c++98-compat-pedantic -Wno-pre-c++17-compat -Wno-pre-c++20-compat -Wno-c++20-compat
        -Wno-covered-switch-default -Wno-padded -Wno-unsafe-buffer-usage-in-libc-call -Wno-shadow-field-in-constructor
>)

function(refl_config TARGET)
    if (CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        target_compile_options(${TARGET} PRIVATE
            "-fplugin=$<TARGET_FILE:refl-plugin>")
        target_link_libraries(${TARGET} PRIVATE refl)

        set(refl_plugin_dummy "${CMAKE_CURRENT_BINARY_DIR}/${TARGET}_refl-plugin-dummy")
        add_custom_command(
            OUTPUT "${refl_plugin_dummy}"
            COMMAND ${CMAKE_COMMAND} -E touch "${refl_plugin_dummy}"
            DEPENDS $<TARGET_FILE:refl-plugin>)
        get_target_property(target_sources ${TARGET} SOURCES)
        set_source_files_properties(${target_sources} PROPERTIES
            OBJECT_DEPENDS "${refl_plugin_dummy}")
    else()
        message(WARNING "refl-plugin can only be used when CMAKE_CXX_COMPILER is Clang")
    endif()
endfunction()

if (REFL_ENABLE_TESTING)
    enable_testing()
    add_subdirectory(tests)
endif()

if (REFL_BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()
