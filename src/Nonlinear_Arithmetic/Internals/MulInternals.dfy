// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* lemmas and functions in this file are used in the proofs in Mul.dfy */

include "GeneralInternals.dfy"
include "MulInternalsNonlinear.dfy"

module MulInternals {

  import opened GeneralInternals
  import opened MulInternalsNonlinear

  /* performs multiplication for positive integers using recursive addition */
  function {:opaque} mul_pos(x: int, y: int) : int
    requires x >= 0
  {
    if x == 0 then 0
    else y + mul_pos(x - 1, y)
  }

  /* performs multiplication for both positive and negative integers */ 
  function mul_recursive(x: int, y: int) : int
  {
    if x >= 0 then mul_pos(x, y)
    else -1 * mul_pos(-1 * x, y)
  }

  /* performs induction on multiplication */ 
  lemma lemma_mul_induction(f: int -> bool)
    requires f(0)
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    forall i ensures f(i) { lemma_induction_helper(1, f, i); }
  }

  /* proves that multiplication is always commutative */
  lemma lemma_mul_commutes()
    ensures  forall x:int, y:int {:trigger x * y} :: x * y == y * x
  {
    forall x:int, y:int
      ensures x * y == y * x
    {
      lemma_mul_induction(i => x * i == i * x);
    }
  }

  /* proves the distributive property of multiplication when multiplying an interger
  by (x +/- 1) */
  //rename for both directions ???
  lemma lemma_mul_successor()
    ensures forall x:int, y:int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x:int, y:int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
    lemma_mul_commutes();
    forall x:int, y:int
      ensures (x + 1) * y == x * y + y
      ensures (x - 1) * y == x * y - y
    {
      lemma_mul_is_distributive_add(y, x, 1);
      lemma_mul_is_distributive_add(y, x, -1);
    }
  }

  /* proves the distributive property of multiplication */
  lemma lemma_mul_distributes()
    ensures forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
    lemma_mul_successor();
    forall x:int, y:int, z:int
      ensures (x + y) * z == x * z + y * z
      ensures (x - y) * z == x * z - y * z
    {
      var f1 := i => (x + i) * z == x * z + i * z;
      var f2 := i => (x - i) * z == x * z - i * z;
      assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
      assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
      assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
      assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
      lemma_mul_induction(f1);
      lemma_mul_induction(f2);
      assert f1(y);
      assert f2(y);
    }
  }

  /* groups distributive and associative properties of multiplication */
  predicate mul_auto()
  {
    && (forall x:int, y:int {:trigger x * y} :: x * y == y * x)
    && (forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z)
    && (forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z)
  }

  /* proves that mul_auto is valid */
  lemma lemma_mul_auto()
    ensures  mul_auto()
  {
    lemma_mul_commutes();
    lemma_mul_distributes();
  }

  /* performs auto induction for multiplication */
  lemma lemma_mul_induction_auto(x: int, f: int -> bool)
    requires mul_auto() ==> f(0)
                          && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + 1))
                          && (forall i {:trigger is_le(i, 0)} :: is_le(i, 0) && f(i) ==> f(i - 1))
    ensures  mul_auto()
    ensures  f(x)
  {
    lemma_mul_commutes();
    lemma_mul_distributes();
    assert forall i {:trigger f(i)} :: is_le(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: is_le(i, 0) && f(i) ==> f(i - 1);
    lemma_mul_induction(f);
    assert f(x);
  }

  /* performs auto induction on multiplication for all i s.t. f(i) exists */
  lemma lemma_mul_induction_auto_forall(f: int -> bool)
    requires mul_auto() ==> f(0)
                          && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + 1))
                          && (forall i {:trigger is_le(i, 0)} :: is_le(i, 0) && f(i) ==> f(i - 1))
    ensures  mul_auto()
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemma_mul_commutes();
    lemma_mul_distributes();
    assert forall i {:trigger f(i)} :: is_le(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: is_le(i, 0) && f(i) ==> f(i - 1);
    lemma_mul_induction(f);
  } 

} 