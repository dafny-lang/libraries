/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

include "../../../src/Collections/Sets/Sets.dfy"

module {:options "-functionSyntax:4"} SetsExamples {

  import opened Sets

  method TestExtract() {
    var s: set<int> := {0, 1};
    var t: set<int> := {0};

    var x := ExtractFromNonEmptySet(s);
    assert x == 0 || x == 1;
    // assert x == 0; this fails due to non-deterministic
    // assert x == 1; this fails due to non-deterministicy

    var y := ExtractFromSingleton(t);
    assert y == 0;

    // var z := ExtractFromSingleton(s); fails as s is not a singleton
  }

}