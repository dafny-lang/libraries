// RUN: %dafny /compile:0 "%s"

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
}