/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:options "-functionSyntax:4"} Dafny.Random {

    // Return an arbitrary boolean value.
    predicate {:extern "DafnyLibraries.Random", "nextBool"} nextBool()

    // Return an arbitrary integer value in the range [0, bound).  If the optional
    // bound is omitted, return an arbitrary nonnegative integer (generally limited
    // to a 64-bit integer value when compiled).
    function {:extern "DafnyLibraries.Random", "nextInt"} nextInt(bound: int := 0): (value: int)
        ensures 0 <= value
        ensures bound > 0 ==> value < bound

    // Return an arbitrary real value in the range [0,1).
     function {:extern "DafnyLibraries.Random", "nextReal"} nextReal(): (value: real)
        ensures 0.0 <= value < 1.0

}
