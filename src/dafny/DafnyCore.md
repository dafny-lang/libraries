
# Guide to the Dafny Core Library

_THIS DOCUMENT IS A DRAFT UNDER ACTIVE DEBATE AND EDITING_

The Dafny programming language and tool set includes
libraries that provide functionality in various domains. This document describes 
the _Dafny Core Library_. Dafny programs are composed of modules; to ensure
verification soundness, Dafny imposes a strict non-circular dependency relationship
among modules. This Core library contains functionality that may be needed
by other libraries, but it itself is standalone.

All the supported, delivered libraries will
- be stable --- a minimum of backwards incompatible changes
- be verified --- proved to meet specifications and tested with expected use cases,
with each release of the library and of the Dafny toolset
- be efficient --- efficient in both proofs and executables that use the libraries
- be compilable for every supported target language by default, with exceptions being documented and for exceptional reasons

The Dafny code for the library is written to be understandable with a minimum of inline documentation
and is open source and available [on github](https://github.com/dafny-lang/libraries). This document is
meant to be tutorial and example-based.

## Content of the Core Library

The sections below describe how to use each of the principal modules of the library:
- [Dafny.Boxes](#sec-boxes) -- containers that enable encapsulaton of success and failure results in a single datatype
- [Bafny.BoundedInts](#sec-boundedints) -- definitions of types and constants for bounded integer arithmetic
- [Dafny.FileIO](#sec-fileio) -- basic input and output operations
- [Dafny.Math](#sec-math) --- basic mathematical operations and lemmas
- [Dafny.Unicode](#sec-unicode) --- tools to manipulate unicode characters and strings
- [Dafny.Collections](#sec-collections) -- functions and lemmas about sequences, sets and maps
- [Dafny.NonlinearArith](sec-nonlinear-arith) --  lemmas and functions for non-linear arithmetic
- [Dafny.Relations](#sec-relations) -- predicates and lemmas about properties of functions


## How to use the library

One uses the library on the command-line by including a path to the library in the `--library` option.

At present, you must have a copy of the library in your file system to use the library. Either
- obtain a release zip file from [the library github release page](https://github.com/dafny-lang/libraries/releases) and unzip it in a folder of your choice, or
- clone the library repository (`git clone https://github.com/dafny-lang/libraries.git`) to a location of your choice

In either case, the relevant directory to point the `--library` option to is named `dafny`, either at the top of the zip file or at `libraries/src/dafny` in the clone. 

Some functionality is implemented using native target language capabilities (e.g. FileIO). In these cases, a compiled program must also includ the relevant target
language files that are included in this Dafny Core distribution.

The procedure for using library code directly with VSCode is not yet settled. For now make a copy of the library in your system and  'include' the `DafnyCore.md` file.


