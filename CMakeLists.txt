cmake_minimum_required(VERSION 3.25)
project(refl LANGUAGES CXX)
set(CMAKE_CXX_STANDARD 23)

option(REFL_BUILD_EXAMPLES "Build examples" OFF)
option(REFL_ENABLE_TESTING "Enable testing" OFF)

add_library(refl INTERFACE)
target_include_directories(refl INTERFACE
    "${CMAKE_CURRENT_SOURCE_DIR}/include")

find_package(LLVM CONFIG REQUIRED)
find_package(Clang CONFIG REQUIRED)
list(APPEND
    CMAKE_MODULE_PATH
    ${LLVM_CMAKE_DIR}
    ${CLANG_CMAKE_DIR}
)
include(AddLLVM)
include(AddClang)

add_library(refl-plugin MODULE
    src/attribute.cpp
    src/plugin.cpp)

target_compile_options(refl-plugin PRIVATE
    $<$<OR:$<CXX_COMPILER_ID:Clang>>:
        -Weverything
        -Wno-c++98-compat -Wno-c++98-compat-pedantic -Wno-pre-c++17-compat -Wno-pre-c++20-compat -Wno-c++20-compat
        -Wno-covered-switch-default -Wno-padded -Wno-unsafe-buffer-usage-in-libc-call -Wno-shadow-field-in-constructor
>)

add_clang_executable(refl-tool 
    src/attribute.cpp
    src/tool.cpp)

target_compile_options(refl-tool PRIVATE
    $<$<OR:$<CXX_COMPILER_ID:Clang>>:
        -Weverything
        -Wno-c++98-compat -Wno-c++98-compat-pedantic -Wno-pre-c++17-compat -Wno-pre-c++20-compat -Wno-c++20-compat
        -Wno-covered-switch-default -Wno-padded -Wno-unsafe-buffer-usage-in-libc-call -Wno-shadow-field-in-constructor
>)

clang_target_link_libraries(refl-tool
    PRIVATE
    clangAST
#    clangASTMatchers
#    clangBasic
#    clangFrontend
#    clangTooling
#    clangToolingRefactoring
)

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
            OBJECT_DEPENDS "${refl_plugin_dummy}"
            COMPILE_DEFINITIONS "REFL_PLUGIN_LOADED"
        )
    else()
        message(WARNING "refl-plugin can only be used when CMAKE_CXX_COMPILER is Clang")
    endif()
endfunction()

function(refl_config_tool TARGET)
    foreach(INC ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
        list(APPEND REFL_IMPLICIT_INC_DIRS --extra-arg=-I${INC}) 
    endforeach()
    target_link_libraries(${TARGET} PRIVATE refl)
    get_target_property(target_sources ${TARGET} SOURCES)
    foreach(S ${target_sources})
        set(M ${S})
        string(APPEND M ".meta.inc")
        add_custom_command(
            OUTPUT "meta/${M}"
            COMMAND $<TARGET_FILE:refl-tool> ${CMAKE_CURRENT_SOURCE_DIR}/${S} -base-path ${CMAKE_CURRENT_SOURCE_DIR} -meta-path ${CMAKE_CURRENT_BINARY_DIR}/meta --extra-arg=-DREFL_GENERATE --extra-arg=-w ${REFL_IMPLICIT_INC_DIRS}
            DEPENDS ${S}
        )
        add_custom_target(meta_${M} ALL
              DEPENDS "meta/${M}"
        )
        set_source_files_properties(${S} PROPERTIES
            OBJECT_DEPENDS "meta_${M}"
            COMPILE_DEFINITIONS "REFL_META_FILE=\"${CMAKE_CURRENT_BINARY_DIR}/meta/${M}\""
        )
    endforeach()
endfunction()

if (REFL_ENABLE_TESTING)
    enable_testing()
    add_subdirectory(tests)
endif()

if (REFL_BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()

