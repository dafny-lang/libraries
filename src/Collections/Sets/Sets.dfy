// RUN: %dafny /compile:0 "%s"

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

module {:options "-functionSyntax:4"} Sets {

  import opened Functions

  /* Proves that if all elements in set s1 are in set s2, s1 is a subset of s2. */
  lemma LemmaSubset<T>(s1: set<T>, s2: set<T>)
    requires forall x {:trigger x in s2} :: x in s1 ==> x in s2
    ensures s1 <= s2
  {
  }

  /* Proves that if s1 is a subset of s2, then the size of s1 is less than or 
     equal to the size of s2. */
  lemma LemmaSubsetSize<T>(s1: set<T>, s2: set<T>)
    ensures s1 < s2 ==> |s1| < |s2|
    ensures s1 <= s2 ==> |s1| <= |s2|
  {
    if s1 != {} {
      var x :| x in s1;
      LemmaSubsetSize(s1 - {x}, s2 - {x});
    }
  }

  /* Proves that if s1 is a subset of s2 and the size of s1 is equal to the size 
     of s2, then s1 is equal to s2. */
  lemma LemmaSubsetEquality<T>(s1: set<T>, s2: set<T>)
    requires s1 <= s2
    requires |s1| == |s2|
    ensures s1 == s2
    decreases s1, s2
  {
    if s1 == {} {
    } else {
      var x :| x in s1;
      LemmaSubsetEquality(s1 - {x}, s2 - {x});
    }
  }

  /* Proves that a singleton set has a size of 1. */
  lemma LemmaSingletonSize<T>(s: set<T>, x: T)
    requires s == {x}
    ensures |s| == 1
  {
  }

  /* Proves that any two elements in a singleton set are equal to each other. */
  lemma LemmaSingletonEquality<T>(s: set<T>, x1: T, x2: T)
    requires |s| == 1
    requires x1 in s
    requires x2 in s
    ensures x1 == x2
  {
    var s2 := {x1, x2};
    assert s2 <= s;
    assert |s2| <= |s| == 1 by { LemmaSubsetSize(s2, s); }
    if x1 != x2 {
      assert 2 <= 1 by { assert |{x1, x2}| == 2; }
    }
  }

  /* Essentially proves that if there exists a bijection between two sets, then
     the two sets have the same cardinality. That is, if an injective function f 
     is applied to each element of a set s1 to construct the set s2, then s1 and s2
     have the same size. */
  lemma LemmaMapSize<X(!new), Y>(s1: set<X>, s2: set<Y>, f: X-->Y)
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    requires forall x {:trigger f(x)} :: x in s1 <==> f(x) in s2
    requires forall y {:trigger y in s2} :: y in s2 ==> exists x :: x in s1 && y == f(x)
    ensures |s1| == |s2|
  {
    if s1 != {} {
      var x :| x in s1;
      var s3 := s1 - {x};
      var s4 := s2 - {f(x)};
      LemmaMapSize(s3, s4, f);
    }
  }

  /* Returns the set s2 that is the image of an injective function f applied to the set s1. */
  function {:opaque} Map<X(!new), Y>(s1: set<X>, f: X-->Y): (s2: set<Y>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    ensures forall x {:trigger f(x)} :: x in s1 <==> f(x) in s2
    ensures |s1| == |s2|
  {
    var s2 := set x | x in s1 :: f(x);
    LemmaMapSize(s1, s2, f);
    s2
  }

  /* Proves that if a set s2 consists those elements of a set s1 that satisfy a given
     predicate, then size of s2 is less than or equal to the size of s1. */
  lemma LemmaFilterSize<X>(s1: set<X>, s2: set<X>, p: X~>bool)
    requires forall x {:trigger p.requires(x)}{:trigger x in s1} :: x in s1 ==> p.requires(x)
    requires forall x {:trigger p(x)}{:trigger x in s1} :: x in s2 ==> x in s1 && p(x)
    ensures |s2| <= |s1|
    decreases s1, s2
  {
    if s2 != {} {
      var x :| x in s2;
      var s3 := s1 - {x};
      var s4 := s2 - {x};
      LemmaFilterSize(s3, s4, p);
    }
  }

  /* Returns the set s2 of those elements in s1 that satisfy the predicate p. */
  function {:opaque} Filter<X(!new)>(s1: set<X>, p: X~>bool): (s2: set<X>)
    reads p.reads
    requires forall x {:trigger p.requires(x)} {:trigger x in s1} :: x in s1 ==> p.requires(x)
    ensures forall x {:trigger p(x)}{:trigger x in s1} :: x in s2 <==> x in s1 && p(x)
    ensures |s2| <= |s1|
  {
    var s2 := set x | x in s1 && p(x);
    LemmaFilterSize(s1, s2, p);
    s2
  }

  /* Proves that the size of a union of two sets is greater than or equal to the size of
     either individual set. */
  lemma LemmaUnionSize<X>(s1: set<X>, s2: set<X>)
    ensures |s1 + s2| >= |s1|
    ensures |s1 + s2| >= |s2|
  {
    if s2 == {} {
    } else {
      var x :| x in s2;
      if x in s1 {
        var s3 := s1 - {x};
        var s4 := s2 - {x};
        assert s3 + s4 == s1 + s2 - {x};
        LemmaUnionSize(s3, s4);
      } else {
        var s3 := s2 - {x};
        assert s1 + s3 == s1 + s2 - {x};
        LemmaUnionSize(s1, s3);
      }
    }
  }

  /* Returns the set of all the integers in the range [a, b). */
  function {:opaque} SetRange(a: int, b: int): (s: set<int>)
    requires a <= b
    ensures forall i {:trigger i in s} :: a <= i < b <==> i in s
    ensures |s| == b - a
    decreases b - a
  {
    if a == b then {} else {a} + SetRange(a + 1, b)
  }

  /* Returns the set of all the integers in the range [0, n). */
  function {:opaque} SetRangeZeroBound(n: int): (s: set<int>)
    requires n >= 0
    ensures forall i {:trigger i in s} :: 0 <= i < n <==> i in s
    ensures |s| == n
  {
    SetRange(0, n)
  }

  /* Proves that if a set solely contains integers in the range [a, b), then its size is
     bounded by b - a. */
  lemma LemmaBoundedSetSize(s: set<int>, a: int, b: int)
    requires forall i {:trigger i in s} :: i in s ==> a <= i < b
    requires a <= b
    ensures |s| <= b - a
  {
    var range := SetRange(a, b);
    forall x {:trigger x in range}{:trigger x in s} | x in s
      ensures x in range;
    {
    }
    assert s <= range;
    LemmaSubsetSize(s, range);
  }

}
