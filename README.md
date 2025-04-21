# Refl - A Clang plugin for static reflection in C++23

The project consits of a plugin that generates reflection information for marked types and a small header file that provides some basic templates to acces this information.

## Overview
Classes and enums can be marked with the `[[refl::all]]` or `[[refl::none]]` attributes.
A simple example to print the class name and all members variables:

```C++
#include <print>
#include <refl/refl.hpp>

class [[refl::all]] Data {
    int privateMember;
public:
    std::string publicMember;
};

int main() {
    // Access reflection info M
    refl::with<Data>([]<typename M>(){                  
        std::print("Name: {}\n", M::name);
        std::print("Member variables:\n");
        // Iterate over each var V in M
        refl::for_each_variable<M>([]<typename V>(){
            std::print("\t{}", V::name);
        })
    });
}
```

## Features
- Reflect any user defined class or enum
- Access any member, constructor (public, private, protected, static or instance) or base class through compile time constants
- Add user defined tags (compile time structs) to any member or constructor
- Reflect only what is needed (refl::none, refl::include, refl::exclude)
- Name, type, parameters (name and type), virtual/mutable property are all reflected

## Known issues
- While template classes can be reflected, template member function can't be. Furthermore explicit specialization of template function in classes must be explicitly exluded.
- Tags can only be applied using GNU style attributes: `__attribute__((refl_tag(MyTag{})))`. See this [issue]. Also, the 'refl_tag' part must not be hidden behind a macro.
- Direct access to the underlying meta information (`refl::meta<T>`) should be avoided as the compiler (and the language server) will see these as errors even when the plugin is in use.
- Warnings in normal code paths will be issued twice.

## Usage
The plugin must be applied during compilation with the `-fplugin=refl-plugin` switch. The header file must be included before any usage of the library (even before using the attributes).

If the project is included as a CMake subdirectory then the provided `refl_config(TARGET)` function can be used to configure a target. It applies the plugin and sets it up as a dependency for compilation.

The LLVM development libraries must be installed to build the plugin.

```CMake
include(FetchContent)
FetchContent_Declare(
  refl
  GIT_SHALLOW    TRUE
  GIT_REPOSITORY https://github.com/drecouse/refl.git
  GIT_TAG        {COMMIT_HASH}
  SYSTEM)
FetchContent_MakeAvailable(refl)
```

## Examples
Multiple small examples are provided to showcase the capabilities of the library. In increasing order of complexity:
- enums: convert between enum values and names, iterate over each enumerator.
- factory: automatically retrieve a function pointer to call any constructor
- serialization: JSON like serializer for any reflected type.
- deserialize: sample implementation to deserialize the previous output.
- functions: print and call member functions. Member function wrapper that can programatically set the parameters by name in any order.

Note that the examples are not meant to be complete nor production ready. They are just presenting some ideas of what is possible with the library.

## Acknowledgement
The library was inspired by the [fire-llvm] project that used a similar method to apply source code changes directly during compilation.

[issue]: https://github.com/llvm/llvm-project/issues/45791
[fire-llvm]: https://github.com/Time0o/fire-llvm
