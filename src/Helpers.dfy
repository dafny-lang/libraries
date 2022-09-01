// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Wrappers.dfy"
include "UInt.dfy"
include "Relations.dfy"

module Helpers {
  export 
    provides Comparison

  import opened Comparison
  import opened U = UInt
  import Relations
  import opened Wrappers


  /*
   * Here is an example relation and a lemma that says the relation is appropriate for use in
   * lexicographic orderings.
   */

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Relations.Trichotomous(UInt8Less)
    ensures Relations.Transitive(UInt8Less)
  {
  }
  
}

module Helpers.Comparison {
  datatype CompResult = LessThan | Equals | GreaterThan 
}