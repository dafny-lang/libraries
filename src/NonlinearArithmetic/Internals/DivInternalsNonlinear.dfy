// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* WARNING: In general, you shouldn't need to call these directly. These are used in the proofs in Div-Internals */

module DivInternalsNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear verification
  is highly unstable! */

  /* zero divided by an integer besides 0 is 0 */
  lemma lemma_div_of_0(d:int)
    requires d != 0
    ensures 0 / d == 0
  { 
  }

  /* the quotient of an integer divided by itself is 1 */
  lemma lemma_div_by_self(d:int)
    requires d != 0
    ensures d / d == 1
  { 
  }

  /* dividing a smaller integer by a larger integer results in a quotient of 0  */
  lemma lemma_small_div()
    ensures forall x, d {:trigger x / d} :: 0 <= x < d && d > 0 ==> x / d == 0
  { 
  }

  /* the quotient of dividing a positive real number (not 0) by a smaller positive real number
  will be greater than 1 */ 
  lemma lemma_real_div_gt(x:real, y:real)
    requires x > y
    requires x >= 0.0
    requires y > 0.0
    ensures  x / y > 1 as real
  { 
  }
  
}