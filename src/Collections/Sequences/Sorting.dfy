// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../StandardLibrary.dfy"
include "../../UInt.dfy"
include "../Sequences/Seq.dfy"
include "../../Lexicographics.dfy"

module Sorting {
  export
    provides SortedBy, MergeSortBy, MergeSortedBy
    provides StandardLibrary, UInt, Lexicographics

  import StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Seq
  import opened Lexicographics

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
