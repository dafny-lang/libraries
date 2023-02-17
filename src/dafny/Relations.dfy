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

}
