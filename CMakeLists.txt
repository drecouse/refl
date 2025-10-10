cmake_minimum_required(VERSION 3.25)
project(refl LANGUAGES CXX)
set(CMAKE_CXX_STANDARD 23)

option(REFL_BUILD_EXAMPLES "Build examples" OFF)
option(REFL_ENABLE_TESTING "Enable testing" OFF)

set(REFL_BINARY_DIR ${CMAKE_CURRENT_BINARY_DIR})

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

target_include_directories(refl-plugin SYSTEM PRIVATE 
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
)

clang_target_link_libraries(refl-plugin
    PRIVATE
    clangAST
    clangSema
    clangASTMatchers
    clangBasic
    clangFrontend
    clangRewrite
    clangCodeGen
)

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
    clangSema
    clangTooling
    clangDependencyScanning
)

target_include_directories(refl-tool SYSTEM PRIVATE 
    ${LLVM_INCLUDE_DIRS}
    ${CLANG_INCLUDE_DIRS}
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

function(refl_config_source SOURCE)
    set(REFL_IMPLICIT_INC_DIRS "")
    if (UNIX)
        foreach(INC ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
            list(APPEND REFL_IMPLICIT_INC_DIRS --extra-arg=-I${INC}) 
        endforeach()
    endif()
    set(META_SOURCE ${SOURCE})
    string(APPEND META_SOURCE ".meta.inc")
    string(MAKE_C_IDENTIFIER ${META_SOURCE} META_SOURCE_ID)
    set(SOURCE_DEP "${CMAKE_CURRENT_BINARY_DIR}/depfiles/${SOURCE}.d")
    set(META_SOURCE "${CMAKE_CURRENT_BINARY_DIR}/meta/${META_SOURCE}")
    add_custom_command(
        OUTPUT ${META_SOURCE}
        COMMAND $<TARGET_FILE:refl-tool>
            ${CMAKE_CURRENT_SOURCE_DIR}/${SOURCE}
            -p ${CMAKE_BINARY_DIR}
            -base-path ${CMAKE_CURRENT_SOURCE_DIR}
            -meta-path ${CMAKE_CURRENT_BINARY_DIR}/meta
            --extra-arg=-DREFL_GENERATE
            --extra-arg=-w
            -compilation-database=${CMAKE_BINARY_DIR}/compile_commands.json
            -dependency-output=${SOURCE_DEP}
            ${REFL_IMPLICIT_INC_DIRS}
        DEPENDS ${SOURCE}
        DEPFILE ${SOURCE_DEP}
    )
    add_custom_target(meta_${META_SOURCE_ID} ALL
        DEPENDS ${META_SOURCE}
    )
    set_source_files_properties(${SOURCE} PROPERTIES
        OBJECT_DEPENDS "meta_${META_SOURCE_ID}"
        COMPILE_DEFINITIONS "REFL_META_FILE=\"${META_SOURCE}\""
    )
endfunction()

function(refl_config_sources SOURCE_FILES)
    foreach(SOURCE_FILE ${SOURCE_FILES})
        refl_config_source(${SOURCE_FILE})
    endforeach()
endfunction()

function(refl_config_tool TARGET)
    target_link_libraries(${TARGET} PRIVATE refl)
    get_target_property(TARGET_SOURCES ${TARGET} SOURCES)
    refl_config_sources("${TARGET_SOURCES}")
endfunction()

if (REFL_ENABLE_TESTING)
    enable_testing()
    add_subdirectory(tests)
endif()

if (REFL_BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()

