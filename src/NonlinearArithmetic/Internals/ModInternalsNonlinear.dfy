// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/***********************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
************************************************************************************/

/* WARNING: In general, you shouldn't need to call these directly. These are used in the proofs in Mod-Internals */

module ModInternalsNonlinear {
  
  /* WARNING: Think three times before adding to this file, as nonlinear verification
  is highly unstable! */

  /* the remainder of 0 divided by an integer is 0 */
  lemma lemmaModOfZeroIsZero(m:int)
    requires 0 < m
    ensures 0 % m == 0
  { 
  }

  /* describes fundementals of the modulus operator */
  lemma lemmaFundamentalDivMod(x:int, d:int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
  {
  }

  /* the remained of 0 divided by any integer is always 0 */
  lemma lemma0ModAnything()
    ensures forall m: int {:trigger 0 % m} :: m > 0 ==> 0 % m == 0
  {
  }

  /* a natural number x divided by a larger natural number gives a remainder equal to x */
  lemma lemmaSmallMod(x:nat, m:nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
  {
  }

  /* the range of the modulus of any integer will be [0, m) where m is the divisor */
  lemma lemmaModRange(x:int, m:int)
    requires m > 0
    ensures 0 <= x % m < m
  {
  }

}