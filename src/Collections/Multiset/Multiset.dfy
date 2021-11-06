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

  /* proves that the cardinality of a multiset is always more than or equal to that
  of the conversion to a set */
  lemma LemmaCardinalityOfSetBound<T>(m: multiset<T>)
    ensures |ToSet(m)| <= |m| 
  {
    reveal ToSet();
    if |m| == 0 {
    } else {
      var x :| x in m;
      var xs := multiset{}[x := m[x]];
      assert ToSet(xs) == {x};
      var rest := m - xs;
      LemmaCardinalityOfSetBound(rest);
      assert ToSet(m) == ToSet(xs) + ToSet(rest);
    }
  }

  lemma LemmaCardinalityOfSetWithDuplicates<T>(m: multiset<T>, x: T)
    requires m[x] > 1
    ensures |ToSet(m)| < |m| 
  {
    reveal ToSet();
    var xs := multiset{}[x := m[x]];
    assert ToSet(xs) == {x};
    var rest := m - xs;
    LemmaCardinalityOfSetBound(rest);
    assert ToSet(m) == ToSet(xs) + ToSet(rest);
    assert |xs| > 1;
  }
}
