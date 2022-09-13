// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../Relations/Relations.dfy"

module Seq.MergeSort {

  import opened Relations

  //Splits a sequence in two, sorts the two subsequences using itself, and merge the two sorted sequences using `MergeSortedWith`
  function method MergeSortBy<T>(a: seq<T>, compare: (T, T) -> bool): (result :seq<T>)
    requires TotalOrdering(compare)
    ensures multiset(a) == multiset(result)
    ensures SortedBy(result, compare)
  {
    if |a| <= 1 then
      a
    else
      var splitIndex := |a| / 2;
      var left, right := a[..splitIndex], a[splitIndex..];

      assert a == left + right;

      var leftSorted := MergeSortBy(left, compare);
      var rightSorted := MergeSortBy(right, compare);

      MergeSortedWith(leftSorted, rightSorted, compare)
  }

  function method {:tailrecursion} MergeSortedWith<T>(left: seq<T>, right: seq<T>, compare: (T, T) -> bool) : (result :seq<T>)
    requires SortedBy(left, compare)
    requires SortedBy(right, compare)
    requires TotalOrdering(compare)
    ensures multiset(left + right) == multiset(result)
    ensures SortedBy(result, compare)
  {
    if |left| == 0 then
      right
    else if |right| == 0 then
      left
    else if compare(left[0], right[0]) then
      LemmaNewFirstElementStillSortedBy(left[0], MergeSortedWith(left[1..], right, compare), compare);
      assert left == [left[0]] + left[1..];

      [left[0]] + MergeSortedWith(left[1..], right, compare)

    else
      LemmaNewFirstElementStillSortedBy(right[0], MergeSortedWith(left, right[1..], compare), compare);
      assert right == [right[0]] + right[1..];

      [right[0]] + MergeSortedWith(left, right[1..], compare)
  }
}