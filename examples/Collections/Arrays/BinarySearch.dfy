// RUN: %dafny /compile:3 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../../src/Relations.dfy"
include "../../../src/Collections/Arrays/BinarySearch.dfy"
include "../../../src/Collections/Sequences/Seq.dfy"
include "../../../src/Collections/Sequences/MergeSort.dfy"

module BinarySearchExamples {

  import BinarySearch
  import opened Seq
  import opened Seq.MergeSort
  import opened Relations

  method SortAndSearch() {
    var input := [1, 7, 7, 3, 9, 0, -6];
    
    var sortedInput := MergeSortBy(input, (x, y) => x <= y);
    print sortedInput, "\n";

    var sortedArray := ToArray(sortedInput);
    var indexOfThree := BinarySearch.BinarySearch(sortedArray, 3, (x, y) => x < y);
    print indexOfThree, "\n";
  }

  method Main() {
    SortAndSearch();
  }
}