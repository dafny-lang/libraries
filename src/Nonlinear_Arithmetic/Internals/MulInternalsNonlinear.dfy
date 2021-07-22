// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* WARNING: In general, you shouldn't need to call these directly. These are used in the proofs in Mul-Internals*/

module MulInternalsNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear verification
  is highly unstable! */

  /* multiplying two positive integers will result in a positive integer */
  lemma lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
  {}

  /* multiplying two nonzero integers will never result in 0 as the poduct */
  lemma lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {}

  /* multiplication is associative */
  lemma lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  {}

  /* multiplication is distributive */
  lemma lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {}

  /* the product of two integers is greater than the value of each individual integer */ 
  lemma lemma_mul_ordering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {}

  /* multiplying by a positive integer preserves inequality */
  lemma lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures  x * z < y * z
  {}

} 