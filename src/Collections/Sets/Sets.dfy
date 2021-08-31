// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Original Copyright under the following: 
*  Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, 
*  ETH Zurich, and University of Washington
*  SPDX-License-Identifier: BSD-2-Clause 
* 
*  Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT 
* 
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../Functions.dfy"

module Sets {

  import opened Functions

  /* If all elements in set x are in set y, x is a subset of y. */
  lemma LemmaSubset<T>(x: set<T>, y: set<T>)
    requires forall e {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
  {
  }

  /* If x is a subset of y, then the size of x is less than or equal to the
  size of y. */
  lemma LemmaSubsetSize<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
  {
    if x != {} {
      var e :| e in x;
      LemmaSubsetSize(x - {e}, y - {e});
    }
  }

  /* If x is a subset of y and the size of x is equal to the size of y, x is
  equal to y. */
  lemma LemmaSubsetEquality<T>(x: set<T>, y: set<T>)
    requires x <= y
    requires |x| == |y|
    ensures x == y
    decreases x, y
  {
    if x == {} {
    } else {
      var e :| e in x;
      LemmaSubsetEquality(x - {e}, y - {e});
    }
  }

  /* A singleton set has a size of 1. */
  lemma LemmaSingletonSize<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
  {
  }

  /* Elements in a singleton set are equal to each other. */
  lemma LemmaSingletonEquality<T>(x: set<T>, a: T, b: T)
    requires |x| == 1
    requires a in x
    requires b in x
    ensures a == b
  {
    if a != b {
      assert {a} < x;
      LemmaSubsetSize({a}, x);
      assert |{a}| < |x|;
      assert |x| > 1;
      assert false;
    }
  }

  /* If an injective function is applied to each element of a set to construct
  another set, the two sets have the same size.  */
  lemma LemmaMapSize<X(!new), Y>(xs: set<X>, ys: set<Y>, f: X-->Y)
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    requires forall x {:trigger f(x)} :: x in xs <==> f(x) in ys
    requires forall y {:trigger y in ys} :: y in ys ==> exists x :: x in xs && y == f(x)
    ensures |xs| == |ys|
  {
    if xs != {} {
      var x :| x in xs;
      var xs' := xs - {x};
      var ys' := ys - {f(x)};
      LemmaMapSize(xs', ys', f);
    }
  }

  /* Map an injective function to each element of a set. */
  function method {:opaque} Map<X(!new), Y>(xs: set<X>, f: X-->Y): (ys: set<Y>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    ensures forall x {:trigger f(x)} :: x in xs <==> f(x) in ys
    ensures |xs| == |ys|
  {
    var ys := set x | x in xs :: f(x);
    LemmaMapSize(xs, ys, f);
    ys
  }

  /* If a set ys is constructed using elements of another set xs for which a
  function returns true, the size of ys is less than or equal to the size of
  xs. */
  lemma LemmaFilterSize<X>(xs: set<X>, ys: set<X>, f: X~>bool)
    requires forall x {:trigger f.requires(x)}{:trigger x in xs} :: x in xs ==> f.requires(x)
    requires forall y {:trigger f(y)}{:trigger y in xs} :: y in ys ==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases xs, ys
  {
    if ys != {} {
      var y :| y in ys;
      var xs' := xs - {y};
      var ys' := ys - {y};
      LemmaFilterSize(xs', ys', f);
    }
  }

  /* Construct a set using elements of another set for which a function returns
  true. */
  function method {:opaque} Filter<X(!new)>(xs: set<X>, f: X~>bool): (ys: set<X>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    ensures forall y {:trigger f(y)}{:trigger y in xs} :: y in ys <==> y in xs && f(y)
    ensures |ys| <= |xs|
  {
    var ys := set x | x in xs && f(x);
    LemmaFilterSize(xs, ys, f);
    ys
  }

  /* The size of a union of two sets is greater than or equal to the size of
  either individual set. */
  lemma LemmaUnionSize<X>(xs: set<X>, ys: set<X>)
    ensures |xs + ys| >= |xs|
    ensures |xs + ys| >= |ys|
  {
    if ys == {} {
    } else {
      var y :| y in ys;
      if y in xs {
        var xr := xs - {y};
        var yr := ys - {y};
        assert xr + yr == xs + ys - {y};
        LemmaUnionSize(xr, yr);
      } else {
        var yr := ys - {y};
        assert xs + yr == xs + ys - {y};
        LemmaUnionSize(xs, yr);
      }
    }
  }

  /* Construct a set with all integers in the range [a, b). */
  function method {:opaque} SetRange(a: int, b: int): (s: set<int>)
    requires a <= b
    ensures forall i {:trigger i in s} :: a <= i < b <==> i in s
    ensures |s| == b - a
    decreases b - a
  {
    if a == b then {} else {a} + SetRange(a + 1, b)
  }

  /* Construct a set with all integers in the range [0, n). */
  function method {:opaque} SetRangeZeroBound(n: int): (s: set<int>)
    requires n >= 0
    ensures forall i {:trigger i in s} :: 0 <= i < n <==> i in s
    ensures |s| == n
  {
    SetRange(0, n)
  }

  /* If a set solely contains integers in the range [a, b), then its size is
  bounded by b - a. */
  lemma LemmaBoundedSetSize(x: set<int>, a: int, b: int)
    requires forall i {:trigger i in x} :: i in x ==> a <= i < b
    requires a <= b
    ensures |x| <= b - a
  {
    var range := SetRange(a, b);
    forall e {:trigger e in range}{:trigger e in x} | e in x
      ensures e in range;
    {
    }
    assert x <= range;
    LemmaSubsetSize(x, range);
  }

}
