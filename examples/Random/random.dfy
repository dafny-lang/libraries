/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

// #RUN: %run --no-verify --target:cs "%s" --input "%S/../../src/Random/Random.cs"
// #RUN: %run --no-verify --target:java "%s" --input "%S/../../src/Random/Random.java"
// #RUN: %run --no-verify --target:js "%s" --input "%S/../../src/Random/Random.js"

include "../../src/Random/Random.dfy"

module RandomExample {
  import Dafny.Random

  method Main(args: seq<string>) {
    var verbose := false;
    if |args| > 1 { verbose := args[1] == "--verbose"; }

    var bvalue := Random.nextBool();
    if verbose { print "Random boolean: ", bvalue, "\n"; }

    var bound := 10;
    var ivalue := Random.nextInt(bound);
    if verbose { print "Random integer from [0,", bound, "): ", ivalue, "\n"; }
    expect 0 <= ivalue < bound, "Random integer not within bounds [0,bound)";

    var lvalue := Random.nextInt();
    if verbose { print "Random integer from [0,MAXINT): ", lvalue, "\n"; }
    expect 0 <= ivalue, "Random unbounded integer not within bounds [0,MAXINT)";

    var rvalue: real := Random.nextReal();
    if verbose { print "Random real from [0,1): ", rvalue, "\n"; }
    expect 0.0 <= rvalue < 1.0, "Random real not within [0,1)";
  }
}
