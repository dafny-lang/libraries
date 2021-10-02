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

  lemma LemmaToSetOfDisjointUnion<T>(a: multiset<T>, b: multiset<T>)
    requires a !! b
    ensures ToSet(a + b) == ToSet(a) + ToSet(b)
  {
  }

  /* proves that the cardinality of a multiset is always more than or equal to that
  of the conversion to a set */
  lemma LemmaCardinalityOfSet<T>(s: multiset<T>)
    ensures |ToSet(s)| <= |s| 
  {
    reveal ToSet();
    if |s| == 0 {
    } else {
      var x :| x in s;
      var xs := multiset{}[x := s[x]];
      assert ToSet(xs) == {x};
      var rest := s - xs;
      LemmaCardinalityOfSet(rest);
      LemmaToSetOfDisjointUnion(xs, rest);
      assert |s| == |xs| + |rest|;
      assert ToSet(s) == ToSet(xs) + ToSet(rest);
    }
  }
}