// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module {:options "-functionSyntax:4"} Dafny.Relations {

  ghost predicate Injective<X(!new), Y>(f: X-->Y)
    reads f.reads
    requires forall x :: f.requires(x)
  {
    forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
  }

  ghost predicate Reflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: R(x, x)
  }

  ghost predicate Irreflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: !R(x, x)
  }

  ghost predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

  ghost predicate Symmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) <==> R(y, x)
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

  ghost predicate PreOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && Transitive(R) 
  }

  ghost predicate PartialOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && Transitive(R) 
    && AntiSymmetric(R)
  }

  /** An element in an ordered set is called a least element (or a minimum), if it is less than 
      every other element of the set. */
  ghost predicate IsLeast<T>(R: (T, T) -> bool, min: T, s: set<T>) {
    min in s && forall x | x in s :: R(min, x)
  }

  /** An element in an ordered set is called a minimal element, if no other element is less than it. */
  ghost predicate IsMinimal<T>(R: (T, T) -> bool, min: T, s: set<T>) {
    min in s && forall x | x in s && R(x, min) :: R(min, x)
  }

  /** An element in an ordered set is called a greatest element (or a maximum), if it is greater than 
      every other element of the set. */
  ghost predicate IsGreatest<T>(R: (T, T) -> bool, max: T, s: set<T>) {
    max in s && forall x | x in s :: R(x, max)
  }

  /** An element in an ordered set is called a maximal element, if no other element is greater than it. */
  ghost predicate IsMaximal<T>(R: (T, T) -> bool, max: T, s: set<T>) {
    max in s && forall x | x in s && R(max, x) :: R(x, max)

  ghost predicate EquivalenceRelation<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && Symmetric(R)
    && Transitive(R)
  }
}
