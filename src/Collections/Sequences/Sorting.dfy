// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../StandardLibrary.dfy"
include "../../UInt.dfy"
include "../Sequences/Seq.dfy"

module Sorting {
  export
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering
    reveals LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow
    provides SortedBy, MergeSortBy, MergeSortedBy
    provides StandardLibrary, UInt

  import StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Seq

  predicate Reflexive<T(!new)>(R: (T, T) -> bool) 
  {
    forall x :: R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) 
  {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool) 
  {
    forall x, y :: R(x, y) || R(y, x)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) 
  {
    && Reflexive(R)
    && AntiSymmetric(R)
    && StandardLibrary.Transitive(R)
    && Connected(R)
  }

  /*
   * Useful orderings
   */

  // reflexivelexicographical comparison of byte sequences
  predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>) 
  {
    LexicographicByteSeqBelowAux(x, y, 0)
  }

  predicate method LexicographicByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    || n == |x|
    || (n != |y| && x[n] < y[n])
    || (n != |y| && x[n] == y[n] && LexicographicByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutLexicographicByteSeqBelow()
    ensures TotalOrdering(LexicographicByteSeqBelow)
  {
    assert Reflexive(LexicographicByteSeqBelow) by {
      forall x, n | 0 <= n <= |x| {
        AboutLexicographicByteSeqBelowAux_Reflexive(x, n);
      }
    }
    assert AntiSymmetric(LexicographicByteSeqBelow) by {
      forall x, y, n: nat |
        n <= |x| && n <= |y| && x[..n] == y[..n] &&
        LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
      {
        AboutLexicographicByteSeqBelowAux_AntiSymmetric(x, y, n);
      }
    }
    assert StandardLibrary.Transitive(LexicographicByteSeqBelow) by {
      forall x, y, z, n: nat |
        n <= |x| && n <= |y| && n <= |z| &&
        LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
      {
        AboutLexicographicByteSeqBelowAux_Transitive(x, y, z, n);
      }
    }
    assert Connected(LexicographicByteSeqBelow) by {
      forall x, y, n: nat | n <= |x| && n <= |y| {
        AboutLexicographicByteSeqBelowAux_Connected(x, y, n);
      }
    }
  }

  lemma AboutLexicographicByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures LexicographicByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
    ensures LexicographicByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures LexicographicByteSeqBelowAux(x, y, n) || LexicographicByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }

  predicate method SortedBy<T>(a: seq<T>,compare: (T, T) -> bool )
  {
    forall i, j | 0 <= i < j < |a| :: compare(a[i],a[j])
  }

  lemma LemmaNewFirstElementStillSortedBy<T>(x: T, s: seq<T>,  compare: (T, T) -> bool) 
    requires SortedBy(s, compare)
    requires |s| == 0 || compare(x,s[0])
  {}

  function method MergeSortBy<T>(a: seq<T>, compare: (T, T) -> bool ): (result :seq<T>)
    requires StandardLibrary.Transitive(compare)
    requires Connected(compare)
    ensures multiset(a) == multiset(result)
    ensures SortedBy(result,compare)

  {
    if |a| <= 1 then
      a
    else
      var splitIndex := |a| / 2;
      var left, right := a[..splitIndex], a[splitIndex..];

      assert a == left + right;

      var leftSorted := MergeSortBy(left, compare);
      var rightSorted := MergeSortBy(right, compare);
      
      MergeSortedBy(leftSorted, rightSorted, compare)
  }

  function method {:tailrecursion} MergeSortedBy<T>(left: seq<T>, right: seq<T>,  compare: (T, T) -> bool) : (result :seq<T>)
    requires SortedBy(left,compare)
    requires SortedBy(right,compare)
    requires StandardLibrary.Transitive(compare)
    requires Connected(compare)
    ensures multiset(left + right) == multiset(result)
    ensures SortedBy(result,compare)
  {
    if |left| == 0 then
      right
    else if |right| == 0 then
      left
    else if compare(right[0],left[0]) then
      LemmaNewFirstElementStillSortedBy(right[0], MergeSortedBy(left, right[1..], compare), compare);
      assert right == [right[0]] + right[1..];

      [right[0]] + MergeSortedBy(left, right[1..], compare)

    else
      LemmaNewFirstElementStillSortedBy(left[0], MergeSortedBy(left[1..], right, compare), compare);
      assert left == [left[0]] + left[1..];

      [left[0]] +  MergeSortedBy(left[1..], right, compare)
  }

  method Sort<T>(s: seq<T>, compare: (T, T) -> bool) returns (result :seq<T>)
    ensures multiset(s) == multiset(result)
    requires StandardLibrary.Transitive(compare)
    requires Connected(compare)
 { 
    result := MergeSortBy(s,compare);
 }
}
