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

  ghost predicate EquivalenceRelation<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && Symmetric(R)
    && Transitive(R)
  }

  ghost predicate SortedBy<T>(a: seq<T>, lessThan: (T, T) -> bool) {
    forall i, j | 0 <= i < j < |a| :: lessThan(a[i], a[j])
  }

  /* An element in an ordered set is called minimal, if it is less than every element of the set. */
  ghost predicate IsMinimum<T>(R: (T, T) -> bool, m: T, s: set<T>) 
  {
    m in s && forall y: T | y in s :: R(m, y)
  }

  /* Any totally ordered set contains a unique minimal element. */
  lemma LemmaUniqueMinimum<T(!new)>(R: (T, T) -> bool, s: set<T>) 
    requires &&|s| > 0 
             && TotalOrdering(R)
    ensures && (exists m: T :: IsMinimum(R, m, s))
            && (forall m, n: T :: IsMinimum(R, m, s) && IsMinimum(R, n, s) ==> m == n)
  {
    var x :| x in s;
    if s == {x} {
      assert IsMinimum(R, x, s);
    } else {
      var s' := s - {x};
      LemmaUniqueMinimum(R, s');
      var z :| IsMinimum(R, z, s');
      if 
      case R(z, x) => {
        forall y: T | y in s ensures R(z, y) {
        }
        assert IsMinimum(R, z, s); 
      }
      case R(x, z) => {
        forall y: T | y in s ensures R(x, y) {
        }
        assert IsMinimum(R, x, s); 
      }
    assert exists m: T :: IsMinimum(R, m, s);
    }
  }

  lemma LemmaNewFirstElementStillSortedBy<T>(x: T, s: seq<T>, lessThan: (T, T) -> bool) 
    requires SortedBy(s, lessThan)
    requires |s| == 0 || lessThan(x, s[0])
    requires TotalOrdering(lessThan)
    ensures SortedBy([x] + s, lessThan)
  {}  
}