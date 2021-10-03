// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Multiset {

  /* converts a multiset to a set */
  function method {:opaque} ToSet<T>(s: multiset<T>): set<T> 
  {
    set x: T | x in s
  }

  lemma LemmaSingletonSize<T>(s: multiset<T>, e: T)
    requires e in s
    requires forall e' | e' in s && e' != e :: s[e'] == 0
    decreases s[e]
    ensures |s| == s[e]
  {
    reveal ToSet();
    if s[e] == 1 {
      assert s == multiset{e};
    } else {
      var s' := s[e := s[e] - 1];
      LemmaSingletonSize(s', e);
    }
  }

  /* proves that the cardinality of a multiset is always more than or equal to that
  of the conversion to a set */
  lemma LemmaCardinalityOfSetBound<T>(s: multiset<T>)
    ensures |ToSet(s)| <= |s| 
  {
    reveal ToSet();
    if |s| == 0 {
    } else {
      var x :| x in s;
      var xs := multiset{}[x := s[x]];
      assert ToSet(xs) == {x};
      var rest := s - xs;
      LemmaCardinalityOfSetBound(rest);
      assert ToSet(s) == ToSet(xs) + ToSet(rest);
    }
  }

  lemma LemmaCardinalityOfSet<T>(s: multiset<T>, e: T)
    requires s[e] > 1
    ensures |ToSet(s)| < |s| 
  {
    reveal ToSet();
    if |s| == 0 {
    } else {
      var x :| x in s && s[x] > 1;
      var xs := multiset{}[x := s[x]];
      assert ToSet(xs) == {x};
      var rest := s - xs;
      LemmaCardinalityOfSetBound(rest);
      assert ToSet(s) == ToSet(xs) + ToSet(rest);
      assert ToSet(xs) !! ToSet(rest);
      assert |ToSet(s)| == |ToSet(xs)| + |ToSet(rest)|;
      assert |ToSet(s)| <= |ToSet(xs)| + |rest|;
      assert |xs| > 1;
    }
  }
}