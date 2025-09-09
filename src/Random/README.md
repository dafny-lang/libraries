# Dafny.Random

## Overview

The `Dafny.Random` module provides a uniform interface to random values across target languages.

```
    // Return an arbitrary boolean value
    predicate nextBool()

    // Return an arbitrary integer value in the range [0, bound)
    function nextInt(bound: int := 0): (value: int)
        ensures 0 <= value
        ensures bound > 0 ==> value < bound

    // Return an arbitrary real value in the range [0,1)
     function nextReal(): (value: real)
        ensures 0.0 <= value < 1.0
```
To see the need for a uniform interface to probability,
C# provides random integer values and Java and JavaScript provide random real values,
and Dafny actually models real numbers as rationals with integral numerators and denominators
of arbitrary size.
This module gives one interface to these various sources of randomness.
This is a simple interface to probability.
For a more sophisticated treatment of probability, see
the [Verified Monte Carlo (VMC)](https://github.com/dafny-lang/Dafny-VMC) library.

The `Dafny.Random` module also provides a uniform interface to nondeterminism and probability.
For example, `nextInt(10)` returns an arbitrary integer from [0,10), but

* in a proof context, the integer is chosen nondeterministcally, and
* in a compiled code context, the integer is chose probabilistically according to the uniform probability distribution.

Compare this with the Dafny construct `var value: int := *;` where value is arbitrary in a proof context and
constant (typically 0) in compiled code.

## Usage

The `Random` module, like `FileIO` will not compile or run correctly without a language-specific
implementation file.  Implementations are currently provided for C#, Java, and JavaScript.
To use `Random` in your code, you must:
* `include` and `import` the `Random` module as you would any other library module
* incorporate the corresponding language-specific implementation file (e.g. `Random.cs`) when building or running your program

The example [random.dfy](../../examples/Random/random.dfy) in the `examples` directory
shows how to use the module.
From the [examples](../../examples/Random) directory, compile and run the file `random.dfy` with

```bash
# C#
$ dafny run random.dfy --target cs --input ../../src/Random/Random.cs -- --verbose

# Java
$ dafny run random.dfy --target java --input ../../src/Random/Random.java -- --verbose

# JavaScript
$ dafny run random.dfy --target js --input ../../src/Random/Random.js -- --verbose
```

If you aren't using `dafny run` to run your program, you will have to integrate the
appropriate language-specific implementation file into your build system.
