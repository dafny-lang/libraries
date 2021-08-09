// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/***********************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
************************************************************************************/

/* lemmas and functions in this file are used in the proofs in Mul.dfy */

include "GeneralInternals.dfy"
include "MulInternalsNonlinear.dfy"

module MulInternals {

  import opened GeneralInternals
  import opened MulInternalsNonlinear

  /* performs multiplication for positive integers using recursive addition */
  function {:opaque} mulPos(x: int, y: int) : int
    requires x >= 0
  {
    if x == 0 then 0
    else y + mulPos(x - 1, y)
  }

  /* performs multiplication for both positive and negative integers */ 
  function mulRecursive(x: int, y: int) : int
  {
    if x >= 0 then mulPos(x, y)
    else -1 * mulPos(-1 * x, y)
  }

  /* performs induction on multiplication */ 
  lemma lemmaMulInduction(f: int -> bool)
    requires f(0)
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    forall i ensures f(i) { lemmaInductionHelper(1, f, i); }
  }

  /* proves that multiplication is always commutative */
  lemma lemmaMulCommutes()
    ensures  forall x:int, y:int {:trigger x * y} :: x * y == y * x
  {
    forall x:int, y:int
      ensures x * y == y * x
    {
      lemmaMulInduction(i => x * i == i * x);
    }
  }

  /* proves the distributive property of multiplication when multiplying an interger
  by (x +/- 1) */
  //rename for both directions ???
  lemma lemmaMulSuccessor()
    ensures forall x:int, y:int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x:int, y:int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
    lemmaMulCommutes();
    forall x:int, y:int
      ensures (x + 1) * y == x * y + y
      ensures (x - 1) * y == x * y - y
    {
      lemmaMulIsDistributiveAdd(y, x, 1);
      lemmaMulIsDistributiveAdd(y, x, -1);
    }
  }

  /* proves the distributive property of multiplication */
  lemma lemmaMulDistributes()
    ensures forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
    lemmaMulSuccessor();
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
      lemmaMulInduction(f1);
      lemmaMulInduction(f2);
      assert f1(y);
      assert f2(y);
    }
  }

  /* groups distributive and associative properties of multiplication */
  predicate mulAuto()
  {
    && (forall x:int, y:int {:trigger x * y} :: x * y == y * x)
    && (forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z)
    && (forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z)
  }

  /* proves that mulAuto is valid */
  lemma lemmaMulAuto()
    ensures  mulAuto()
  {
    lemmaMulCommutes();
    lemmaMulDistributes();
  }

  /* performs auto induction for multiplication */
  lemma lemmaMulInductionAuto(x: int, f: int -> bool)
    requires mulAuto() ==> f(0)
                          && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + 1))
                          && (forall i {:trigger isLe(i, 0)} :: isLe(i, 0) && f(i) ==> f(i - 1))
    ensures  mulAuto()
    ensures  f(x)
  {
    lemmaMulCommutes();
    lemmaMulDistributes();
    assert forall i {:trigger f(i)} :: isLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: isLe(i, 0) && f(i) ==> f(i - 1);
    lemmaMulInduction(f);
    assert f(x);
  }

  /* performs auto induction on multiplication for all i s.t. f(i) exists */
  lemma lemmaMulInductionAutoForall(f: int -> bool)
    requires mulAuto() ==> f(0)
                          && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + 1))
                          && (forall i {:trigger isLe(i, 0)} :: isLe(i, 0) && f(i) ==> f(i - 1))
    ensures  mulAuto()
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemmaMulCommutes();
    lemmaMulDistributes();
    assert forall i {:trigger f(i)} :: isLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: isLe(i, 0) && f(i) ==> f(i - 1);
    lemmaMulInduction(f);
  } 

} 