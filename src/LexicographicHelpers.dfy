// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Relations.dfy"
include "Lexicographics.dfy"

module LexicographicHelpers{
    export 
        provides UInt

    import opened Relations
    import opened Lexicographics
    import opened Lexicographics.UInt

    lemma LexIsReflexive<T>(a: seq<T>, less: (T, T) -> bool)
    ensures LessOrEqual(a, a, less)
    {
    assert LessOrEqualAux(a, a, less, |a|);
    }

  lemma LexIsAntisymmetric<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    requires LessOrEqual(a, b, less)
    requires LessOrEqual(b, a, less)
    ensures a == b
  {
    assert LessIrreflexive: forall x,y :: less(x, y) ==> x != y by {
      reveal Trich;
    }
    assert ASymmetric: forall x,y :: less(x, y) && less(y, x) ==> false by {
      reveal Trich;
    }
    var k0 :| 0 <= k0 <= |a| && LessOrEqualAux(a, b, less, k0);
    var k1 :| 0 <= k1 <= |b| && LessOrEqualAux(b, a, less, k1);
    var max := if k0 < k1 then k1 else k0;
    assert max <= |a| && max <= |b|;
    assert SameUntilMax: forall i :: 0 <= i < max ==> a[i] == b[i];
    assert AA: k0 == |a| || (k0 < |b| && less(a[k0], b[k0]));
    assert BB: k1 == |b| || (k1 < |a| && less(b[k1], a[k1]));
    calc {
      true;
    ==>  { reveal AA, BB; }
      (k0 == |a| || (k0 < |b| && less(a[k0], b[k0]))) && (k1 == |b| || (k1 < |a| && less(b[k1], a[k1])));
    ==  // distribute && and ||
      (k0 == |a| && k1 == |b|) ||
      (k0 == |a| && k1 < |a| && less(b[k1], a[k1])) ||
      (k0 < |b| && less(a[k0], b[k0]) && k1 == |b|) ||
      (k0 < |b| && less(a[k0], b[k0]) && k1 < |a| && less(b[k1], a[k1]));
    ==  { reveal LessIrreflexive, SameUntilMax; }
      (k0 == |a| && k1 == |b|) ||
      (k0 < |b| && less(a[k0], b[k0]) && k1 < |a| && less(b[k1], a[k1]));
    ==>  { reveal LessIrreflexive, SameUntilMax; assert max <= k0 && max <= k1; }
      (k0 == |a| && k1 == |b|) ||
      (k0 < |b| && less(a[k0], b[k0]) && k1 < |a| && less(b[k1], a[k1]) && k0 == k1 == max);
    ==  { reveal ASymmetric; }
      k0 == |a| && k1 == |b|;
    ==>  { assert |a| == k0 <= max && |b| == k1 <= max ==> k0 == k1; }
      max == |a| == |b|;
    ==>  { reveal SameUntilMax; }
      a == b;
    }
  }

 lemma LexIsTransitive<T>(a: seq<T>, b: seq<T>, c: seq<T>, less: (T, T) -> bool)
    requires Transitive(less)
    requires LessOrEqual(a, b, less)
    requires LessOrEqual(b, c, less)
    ensures LessOrEqual(a, c, less)
  {
    var k0 :| 0 <= k0 <= |a| && LessOrEqualAux(a, b, less, k0);
    var k1 :| 0 <= k1 <= |b| && LessOrEqualAux(b, c, less, k1);
    var k := if k0 < k1 then k0 else k1;
    assert LessOrEqualAux(a, c, less, k);
  }

  lemma LexIsTotal<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    ensures LessOrEqual(a, b, less) || LessOrEqual(b, a, less)
  {
    var m := 0;
    while m < |a| && m < |b| && a[m] == b[m]
      invariant m <= |a| && m <= |b|
      invariant forall i :: 0 <= i < m ==> a[i] == b[i]
    {
      m := m + 1;
    }
    // m is the length of the common prefix of a and b
    if m == |a| == |b| {
      assert a == b;
      LexIsReflexive(a, less);
    } else if m == |a| < |b| {
      assert LessOrEqualAux(a, b, less, m);
    } else if m == |b| < |a| {
      assert LessOrEqualAux(b, a, less, m);
    } else {
      assert m < |a| && m < |b|;
      reveal Trich;
      if
      case less(a[m], b[m]) =>
        assert LessOrEqualAux(a, b, less, m);
      case less(b[m], a[m]) =>
        assert LessOrEqualAux(b, a, less, m);
    }
  }
  /*
   * SetToOrderedSequence(s, less) takes a set of T-strings and returns them as a sequence,
   * ordered by the lexicographic ordering whose underlying irreflexive ordering is "less".
   * The function is compilable, but will not exhibit enviable performance.
   */

  function method {:tailrecursion} SetToOrderedSequence<T(!new,==)>(s: set<seq<T>>, less: (T, T) -> bool): (q: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures |s| == |q|
    ensures forall i :: 0 <= i < |q| ==> q[i] in s
    ensures forall k :: k in s ==> k in q
    ensures forall i :: 0 < i < |q| ==> LessOrEqual(q[i-1], q[i], less)
    ensures forall i, j | 0 <= i < j < |q| :: q[i] != q[j];
  {
    if s == {} then
      []
    else
      // In preparation for the assign-such-that statement below, we'll need to
      // prove that a minimum exists and that it is unique.
      // The following lemma shows existence:
      ThereIsAMinimum(s, less);
      // The following assertion shows uniqueness:
      assert forall a, b :: IsMinimum(a, s, less) && IsMinimum(b, s, less) ==> a == b by {
        // The proof of the assertion is the following forall statement.
        // But why did we even bother to write the assert-by instead of
        // just writing this forall statement in the first place? Because
        // we are in an expression context and a forall statement cannot start
        // an expression (because the "forall" makes the parser think that
        // a forall expression is coming).
        forall a, b | IsMinimum(a, s, less) && IsMinimum(b, s, less) {
          // For the given a and b, the proof is settled by calling the following lemma:
          MinimumIsUnique(a, b, s, less);
        }
      }
      // The "a in s" in the following line follows from IsMinimum(a, s), so it
      // is logically redundant. However, it is needed to convince the compiler
      // that the assign-such-that statement is compilable.
      var a :| a in s && IsMinimum(a, s, less);
      [a] + SetToOrderedSequence(s - {a}, less)
  }

  predicate method IsMinimum<T(==)>(a: seq<T>, s: set<seq<T>>, less: (T, T) -> bool) {
    a in s &&
    forall z :: z in s ==> LessOrEqual(a, z, less)
  }

  lemma ThereIsAMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures exists a :: IsMinimum(a, s, less)
  {
    var a := FindMinimum(s, less);
  }

  lemma MinimumIsUnique<T>(a: seq<T>, b: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    requires IsMinimum(a, s, less) && IsMinimum(b, s, less)
    requires Trichotomous(less)
    ensures a == b
  {
    LexIsAntisymmetric(a, b, less);
  }

  lemma FindMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool) returns (a: seq<T>)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures IsMinimum(a, s, less)
  {
    a :| a in s;
    if s == {a} {
      LexIsReflexive(a, less);
    } else {
      var s' := s - {a};
      assert forall x :: x in s <==> x == a || x in s';
      var a' := FindMinimum(s', less);
      if LessOrEqual(a', a, less) {
        a := a';
      } else {
        assert LessOrEqual(a, a', less) by {
          LexIsTotal(a, a', less);
        }
        forall z | z in s
          ensures LessOrEqual(a, z, less)
        {
          if z == a {
            LexIsReflexive(a, less);
          } else {
            calc {
              true;
            ==  // z in s && z != a
              z in s';
            ==>  // by postcondition of FindMinim(s') above
              LessOrEqual(a', z, less);
            ==>  { LexIsTransitive(a, a', z, less); }
              LessOrEqual(a, z, less);
            }
          }
        }
      }
    }
  }
}