// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../StandardLibrary.dfy"
include "../../UInt.dfy"

module BinarySearch {
  export
    provides StandardLibrary, UInt

  import StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers = StandardLibrary.Wrappers

method BinarySearch<T>(a: array<T>, key: T, compare: (T, T) -> bool) returns (r:Option<nat>)
  requires forall i,j :: 0 <= i < j < a.Length ==> compare(a[i], a[j]) || a[i] == a[j]
  requires StandardLibrary.Trichotomous(compare)
  ensures r.Some? ==> r.value < a.Length && a[r.value] == key
  ensures r.None? ==> key !in a[..]
{
  var lo, hi : nat := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if compare(key , a[mid]) {
      hi := mid;
    } else if compare(a[mid] , key) {
      lo := mid + 1;
    } else {
      return Some(mid);
    }
  }
  return None;
}
}