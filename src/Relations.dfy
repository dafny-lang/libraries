// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module {:options "-functionSyntax:4"} Relations {

  ghost predicate Reflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: R(x, x)
  }

  ghost predicate Irreflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: !R(x, x)
  }

  ghost predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

  ghost predicate Connected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: x != y ==> R(x, y) || R(y, x)
  }

  ghost predicate StronglyConnected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) || R(y, x)
  }

  ghost predicate Transitive<T(!new)>(R: (T, T) -> bool) {
    forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z)
  }

  ghost predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && AntiSymmetric(R)
    && Transitive(R)
    && StronglyConnected(R)
  }

  ghost predicate StrictTotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Irreflexive(R)
    && AntiSymmetric(R)
    && Transitive(R)
    && Connected(R)
  }

  ghost predicate SortedBy<T>(a: seq<T>, lessThan: (T, T) -> bool) {
    forall i, j | 0 <= i < j < |a| :: lessThan(a[i], a[j])
  }

  lemma LemmaNewFirstElementStillSortedBy<T>(x: T, s: seq<T>, lessThan: (T, T) -> bool)
    requires SortedBy(s, lessThan)
    requires |s| == 0 || lessThan(x, s[0])
    requires TotalOrdering(lessThan)
    ensures SortedBy([x] + s, lessThan)
  {}
}
