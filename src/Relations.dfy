// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Relations { 

  predicate Reflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: R(x, x)
  }

  predicate Irreflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: !R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: x != y ==> R(x, y) || R(y, x)
  }

  predicate StronglyConnected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) || R(y, x)
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool) {
    forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && AntiSymmetric(R)
    && Transitive(R)
    && StronglyConnected(R)
  }  

  predicate StrictTotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Irreflexive(R)
    && AntiSymmetric(R)
    && Transitive(R)
    && Connected(R)
  }  

  predicate method SortedBy<T>(a: seq<T>, less: (T, T) -> bool) {
    forall i, j | 0 <= i < j < |a| :: less(a[i], a[j])
  }

  lemma LemmaNewFirstElementStillSortedBy<T>(x: T, s: seq<T>, less: (T, T) -> bool) 
    requires SortedBy(s, less)
    requires |s| == 0 || less(x, s[0])
    requires TotalOrdering(less)
    ensures SortedBy([x] + s, less)
  {}  

  /*
  * To be _trichotomous_ means that for any two `x` and `y`,
  * EXACTLY one of the following three conditions holds:
  *   - less(x, y)
  *   - x == y
  *   - less(y, x)
  * Note that being trichotomous implies being irreflexive.
  */
  predicate Trichotomous<T(!new)>(less: (T, T) -> bool) {
    (forall x, y :: less(x, y) || x == y || less(y, x)) &&  // at least one of the three
    (forall x, y :: less(x, y) && less(y, x) ==> false) &&  // not both of the less's
    (forall x, y :: less(x, y) ==> x != y)  // not a less and the equality
  }
}