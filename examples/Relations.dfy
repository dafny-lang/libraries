// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../src/Relations.dfy"

module RelationsExamples {

  import opened Relations

  lemma BuiltInIntLTIsStrictTotalOrdering()
    ensures StrictTotalOrdering((x: int, y: int) => x < y)
  {}

  lemma BuiltInIntLEIsTotalOrdering()
    ensures TotalOrdering((x: int, y: int) => x <= y)
  {}

  function Modulo(n: nat): (R: (int, int) -> bool)
    requires n >= 1
    ensures EquivalenceRelation(R)
  {
    (x, y) => (x % n ==  y % n)
  }

  lemma BuiltInIntEqIsEquivalenceRelation()
    ensures EquivalenceRelation((x: int, y: int) => (x == y))
  {}

}
