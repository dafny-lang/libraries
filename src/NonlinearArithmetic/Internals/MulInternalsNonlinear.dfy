// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/***********************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
************************************************************************************/

/* WARNING: In general, you shouldn't need to call these directly. These are used in the proofs in Mul-Internals*/

module MulInternalsNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear verification
  is highly unstable! */

  /* multiplying two positive integers will result in a positive integer */
  lemma lemmaMulStrictlyPositive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
  {}

  /* multiplying two nonzero integers will never result in 0 as the poduct */
  lemma lemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {}

  /* multiplication is associative */
  lemma lemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  {}

  /* multiplication is distributive */
  lemma lemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {}

  /* the product of two integers is greater than the value of each individual integer */ 
  lemma lemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {}

  /* multiplying by a positive integer preserves inequality */
  lemma lemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures  x * z < y * z
  {}

} 