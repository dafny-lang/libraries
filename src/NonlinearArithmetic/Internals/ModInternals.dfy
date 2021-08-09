// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/***********************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
************************************************************************************/

/* lemmas and functions in this file are used in the proofs in DivMod.dfy */

include "GeneralInternals.dfy"
include "MulInternals.dfy"
include "../Mul.dfy"
include "ModInternalsNonlinear.dfy"
include "DivInternalsNonlinear.dfy"

module ModInternals {

  import opened GeneralInternals
  import opened Mul
  import opened MulInternalsNonlinear
  import opened MulInternals
  import opened ModInternalsNonlinear
  import opened DivInternalsNonlinear

  /* Performs modulus recursively. */
  function method {:opaque} modRecursive(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then (d - x) else x
  {
    if x < 0 then
      modRecursive(d + x, d)
    else if x < d then
      x
    else
      modRecursive(x - d, d)
  }

  /* performs induction on modulus */ 
  lemma lemmaModInductionForall(n: int, f: int -> bool)
    requires n > 0
    requires forall i :: 0 <= i < n ==> f(i)
    requires forall i {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i {:trigger f(i), f(i - n)} :: i < n  && f(i) ==> f(i - n)
    ensures  forall i :: f(i)
  {
    forall i ensures f(i) { lemmaInductionHelper(n, f, i); }
  }

  /* given an integer x and divisor n, the remainder of x%n is equivalent to the remainder of (x+m)%n
  where m is a multiple of n */
  lemma lemmaModInductionForall2(n: int, f:(int, int)->bool)
    requires n > 0
    requires forall i, j :: 0 <= i < n && 0 <= j < n ==> f(i, j)
    requires forall i, j {:trigger f(i, j), f(i + n, j)} :: i >= 0 && f(i, j) ==> f(i + n, j)
    requires forall i, j {:trigger f(i, j), f(i, j + n)} :: j >= 0 && f(i, j) ==> f(i, j + n)
    requires forall i, j {:trigger f(i, j), f(i - n, j)} :: i < n  && f(i, j) ==> f(i - n, j)
    requires forall i, j {:trigger f(i, j), f(i, j - n)} :: j < n  && f(i, j) ==> f(i, j - n)
    ensures  forall i, j :: f(i, j)
  {
    forall x, y
      ensures f(x, y)
    {
      forall i | 0 <= i < n
        ensures f(i, y)
      {
        var fj := j => f(i, j);
        lemmaModInductionForall(n, fj);
        assert fj(y);
      }
      var fi := i => f(i, y);
      lemmaModInductionForall(n, fi);
      assert fi(x);
    }
  }

  /* proves the basics of the modulus operation */
  lemma lemmaModBasics(n: int)
    requires n > 0
    ensures  forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
    ensures  forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
    ensures  forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures  forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    ensures  forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
  {
    forall x: int
      ensures 0 <= x < n <==> x % n == x
    {
      if (0 <= x < n) { lemmaSmallMod(x, n); }
      lemmaModRange(x, n);
    }
    forall x: int
      ensures (x + n) % n == x % n
      ensures (x - n) % n == x % n
      ensures (x + n) / n == x / n + 1
      ensures (x - n) / n == x / n - 1
    {
      lemmaFundamentalDivMod(x, n);
      lemmaFundamentalDivMod(x + n, n);
      lemmaFundamentalDivMod(x - n, n);
      lemmaModRange(x, n);
      lemmaModRange(x + n, n);
      lemmaModRange(x - n, n);
      var zp := (x + n) / n - x / n - 1;
      var zm := (x - n) / n - x / n + 1;
      forall ensures 0 == n * zp + ((x + n) % n) - (x % n) { lemmaMulAuto(); }
      forall ensures 0 == n * zm + ((x - n) % n) - (x % n) { lemmaMulAuto(); }
      if (zp > 0) { lemmaMulInequality(1, zp, n); }
      if (zp < 0) { lemmaMulInequality(zp, -1, n); }
      if (zp == 0) { lemmaMulBasicsAuto(); }
      if (zm > 0) { lemmaMulInequality(1, zm, n); }
      if (zm < 0) { lemmaMulInequality(zm, -1, n); }
    }
  }

  /* proves the quotient remainder theorem */
  lemma lemmaQuotientAndRemainder(x: int, q: int, r: int, n: int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures  q == x / n
    ensures  r == x % n
    decreases if q > 0 then q else -q
  {
    lemmaModBasics(n);
    lemmaMulIsCommutativeAuto();
    lemmaMulIsDistributiveAddAuto();
    lemmaMulIsDistributiveSubAuto();

    if q > 0 {
      assert q * n + r == (q - 1) * n + n + r;
      lemmaQuotientAndRemainder(x - n, q - 1, r, n);
    }
    else if q < 0 {
      assert q * n + r == (q + 1) * n - n + r;
      lemmaQuotientAndRemainder(x + n, q + 1, r, n);
    }
    else {
      lemmaSmallDiv();
      assert r / n == 0;
    }
  }

  /* automates the modulus operator process */
  predicate modAuto(n: int)
      requires n > 0;
  {
  && (n % n == (-n) % n == 0)
  && (forall x: int {:trigger (x % n) % n} :: (x % n) % n == x % n)
  && (forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x)
  && (forall x: int, y: int {:trigger (x + y) % n} ::
                  (var z := (x % n) + (y % n);
                      (  (0 <= z < n     && (x + y) % n == z)
                      || (n <= z < n + n && (x + y) % n == z - n))))
  && (forall x: int, y: int {:trigger (x - y) % n} ::
                  (var z := (x % n) - (y % n);
                      (   (0 <= z < n && (x - y) % n == z)
                      || (-n <= z < 0 && (x - y) % n == z + n))))
  }

/* ensures that modAuto is true */
  lemma lemmaModAuto(n: int)
    requires n > 0
    ensures  modAuto(n)
  {
    lemmaModBasics(n);
    lemmaMulIsCommutativeAuto();
    lemmaMulIsDistributiveAddAuto();
    lemmaMulIsDistributiveSubAuto();

    forall x: int, y: int {:trigger (x + y) % n}
      ensures var z := (x % n) + (y % n);
              || (0 <= z < n && (x + y) % n == z)
              || (n <= z < 2 * n && (x + y) % n == z - n)
    {
      var xq, xr := x / n, x % n;
      lemmaFundamentalDivMod(x, n);
      assert x == xq * n + xr;
      var yq, yr := y / n, y % n;
      lemmaFundamentalDivMod(y, n);
      assert y == yq * n + yr;
      if xr + yr < n {
        lemmaQuotientAndRemainder(x + y, xq + yq, xr + yr, n);
      }
      else {
        lemmaQuotientAndRemainder(x + y, xq + yq + 1, xr + yr - n, n);
      }
    }

    forall x: int, y: int {:trigger (x - y) % n}
      ensures var z := (x % n) - (y % n);
              || (0 <= z < n && (x - y) % n == z)
              || (-n <= z < 0 && (x - y) % n == z + n)
    {
      var xq, xr := x / n, x % n;
      lemmaFundamentalDivMod(x, n);
      assert x == xq * n + xr;
      var yq, yr := y / n, y % n;
      lemmaFundamentalDivMod(y, n);
      assert y == yq * n + yr;
      if xr - yr >= 0 {
        lemmaQuotientAndRemainder(x - y, xq - yq, xr - yr, n);
      }
      else {
        lemmaQuotientAndRemainder(x - y, xq - yq - 1, xr - yr + n, n);
      }
    }
  }

  /* performs auto induction for modulus */
  lemma lemmaModInductionAuto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires modAuto(n) ==> && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && i < n ==> f(i))
                          && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger isLe(i + 1, n)} :: isLe(i + 1, n) && f(i) ==> f(i - n))
    ensures  modAuto(n)
    ensures  f(x)
  {
    lemmaModAuto(n);
    assert forall i :: isLe(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: isLe(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: isLe(i + 1, n) && f(i) ==> f(i - n);
    lemmaModInductionForall(n, f);
    assert f(x);
  }

  // not used in other files
  /* performs auto induction on modulus for all i s.t. f(i) exists */
  lemma lemmaModInductionAutoForall(n: int, f: int -> bool)
    requires n > 0
    requires modAuto(n) ==> && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && i < n ==> f(i))
                          && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger isLe(i + 1, n)} :: isLe(i + 1, n) && f(i) ==> f(i - n))
    ensures  modAuto(n)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemmaModAuto(n);
    assert forall i :: isLe(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: isLe(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: isLe(i + 1, n) && f(i) ==> f(i - n);
    lemmaModInductionForall(n, f);
  }

} 