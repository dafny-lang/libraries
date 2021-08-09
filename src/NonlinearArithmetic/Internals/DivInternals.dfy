// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/***********************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
************************************************************************************/

/* lemmas and functions in this file are used in the proofs in DivMod.dfy 

Specs/implements mathematical div and mod, not the C version.
This may produce "surprising" results for negative values
For example, -3 div 5 is -1 and -3 mod 5 is 2.
Note this is consistent: -3 * -1 + 2 == 5 */

include "GeneralInternals.dfy"
include "ModInternals.dfy"

module DivInternals {

  import opened GeneralInternals
  import opened ModInternals
  import opened ModInternalsNonlinear
  import opened DivInternalsNonlinear
  import opened MulInternals

  /* Performs division recursively with positive denominator. */
  function method {:opaque} divPos(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then (d - x) else x
  {
    if x < 0 then
      -1 + divPos(x + d, d)
    else if x < d then
      0
    else
      1 + divPos(x - d, d)
  }

  /* Performs division recursively. */
  function {:opaque} divRecursive(x: int, d: int): int
    requires d != 0
  {
    reveal divPos();
    if d > 0 then
      divPos(x, d)
    else
      -1 * divPos(x, -1 * d)
  }

  /* proves the basics of the division operation */
  lemma lemmaDivBasics(n: int)
    requires n > 0
    ensures  n / n == -((-n) / n) == 1
    ensures  forall x:int {:trigger x / n} :: 0 <= x < n <==> x / n == 0
    ensures  forall x:int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures  forall x:int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
  {
    lemmaModAuto(n);
    lemmaModBasics(n);
    lemmaSmallDiv();
    lemmaDivBySelf(n);
    forall x: int | x / n == 0
      ensures 0 <= x < n
    {
      lemmaFundamentalDivMod(x, n);
    }
  }

  /* automates the division operator process */
  predicate divAuto(n: int)
    requires n > 0
  {
    && modAuto(n)
    && (n / n == -((-n) / n) == 1)
    && (forall x: int {:trigger x / n} :: 0 <= x < n <==> x / n == 0)
    && (forall x: int, y: int {:trigger (x + y) / n} ::
          (var z := (x % n) + (y % n);
                    ((0 <= z < n && (x + y) / n == x / n + y / n) ||
                    (n <= z < n + n && (x + y) / n == x / n + y / n + 1))))
    && (forall x: int, y: int {:trigger (x - y) / n} ::
          (var z := (x % n) - (y % n);
                    ((0 <= z < n && (x - y) / n == x / n - y / n) ||
                    (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))))
  }

  /* ensures that divAuto is true */
  lemma lemmaDivAuto(n: int)
    requires n > 0
    ensures  divAuto(n)
  {
    lemmaModAuto(n);
    lemmaDivBasics(n);
    assert (0 + n) / n == 1;
    assert (0 - n) / n == -1;
    forall x:int, y:int {:trigger (x + y) / n}
      ensures  var z := (x % n) + (y % n);
                      (|| (0 <= z < n && (x + y) / n == x / n + y / n)
                        || (n <= z < 2 * n && (x + y) / n == x / n + y / n + 1))
    {
      var f := (xx:int, yy:int) =>
                  (var z := (xx % n) + (yy % n);
                      (   (0 <= z < n && (xx + yy) / n == xx / n + yy / n)
                        || (n <= z < 2 * n && (xx + yy) / n == xx / n + yy / n + 1)));
      forall i, j
        ensures j >= 0 && f(i, j) ==> f(i, j + n)
        ensures i < n  && f(i, j) ==> f(i - n, j)
        ensures j < n  && f(i, j) ==> f(i, j - n)
        ensures i >= 0 && f(i, j) ==> f(i + n, j)
      {
        assert ((i + n) + j) / n == ((i + j) + n) / n;
        assert (i + (j + n)) / n == ((i + j) + n) / n;
        assert ((i - n) + j) / n == ((i + j) - n) / n;
        assert (i + (j - n)) / n == ((i + j) - n) / n;
      }
      forall i, j
        ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
      {
        assert ((i + n) + j) / n == ((i + j) + n) / n;
        assert (i + (j + n)) / n == ((i + j) + n) / n;
        assert ((i - n) + j) / n == ((i + j) - n) / n;
        assert (i + (j - n)) / n == ((i + j) - n) / n;
      }
      lemmaModInductionForall2(n, f);
      assert f(x, y);
    }
    forall x:int, y:int {:trigger (x - y) / n}
      ensures  var z := (x % n) - (y % n);
                      (|| (0 <= z < n && (x - y) / n == x / n - y / n)
                        || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))
    {
      var f := (xx:int, yy:int) =>
                  (var z := (xx % n) - (yy % n);
                      (   (0 <= z < n && (xx - yy) / n == xx / n - yy / n)
                      || (-n <= z < 0 && (xx - yy) / n == xx / n - yy / n - 1)));
      forall i, j
        ensures j >= 0 && f(i, j) ==> f(i, j + n)
        ensures i < n  && f(i, j) ==> f(i - n, j)
        ensures j < n  && f(i, j) ==> f(i, j - n)
        ensures i >= 0 && f(i, j) ==> f(i + n, j)
      {
        assert ((i + n) - j) / n == ((i - j) + n) / n;
        assert (i - (j - n)) / n == ((i - j) + n) / n;
        assert ((i - n) - j) / n == ((i - j) - n) / n;
        assert (i - (j + n)) / n == ((i - j) - n) / n;
      }
      forall i, j
        ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
      {
        assert ((i + n) - j) / n == ((i - j) + n) / n;
        assert (i - (j - n)) / n == ((i - j) + n) / n;
        assert ((i - n) - j) / n == ((i - j) - n) / n;
        assert (i - (j + n)) / n == ((i - j) - n) / n;
      }
      lemmaModInductionForall2(n, f);
      assert f(x, y);
    }
  }

  /* performs auto induction for division */
  lemma lemmaDivInductionAuto(n: int, x: int, f: int->bool)
    requires n > 0
    requires divAuto(n) ==> && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && i < n ==> f(i))
                          && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger isLe(i + 1, n)} :: isLe(i + 1, n) && f(i) ==> f(i - n))
    ensures  divAuto(n)
    ensures  f(x)
  {
    lemmaDivAuto(n);
    assert forall i :: isLe(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: isLe(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: isLe(i + 1, n) && f(i) ==> f(i - n);
    lemmaModInductionForall(n, f);
    assert f(x);
  }

  /* performs auto induction on division for all i s.t. f(i) exists */
  lemma lemmaDivInductionAutoForall(n:int, f:int->bool)
    requires n > 0
    requires divAuto(n) ==> && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && i < n ==> f(i))
                          && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger isLe(i + 1, n)} :: isLe(i + 1, n) && f(i) ==> f(i - n))
    ensures  divAuto(n)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemmaDivAuto(n);
    assert forall i :: isLe(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: isLe(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: isLe(i + 1, n) && f(i) ==> f(i - n);
    lemmaModInductionForall(n, f);
  }

} 