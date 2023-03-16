// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

include "../Wrappers.dfy"
include "../Relations.dfy"
include "Seqs.dfy"

module Dafny.Collections.Arrays {

  import opened Wrappers
  import opened Relations
  import opened Seq

  method BinarySearch<T>(a: array<T>, key: T, less: (T, T) -> bool) returns (r: Option<nat>)
    requires SortedBy(a[..], (x, y) => less(x, y) || x == y)
    requires StrictTotalOrdering(less)
    ensures r.Some? ==> r.value < a.Length && a[r.value] == key
    ensures r.None? ==> key !in a[..]
  {
    var lo, hi : nat := 0, a.Length;
    while lo < hi
      invariant 0 <= lo <= hi <= a.Length
      invariant key !in a[..lo] && key !in a[hi..]
      invariant a[..] == old(a[..])
    {
      var mid := (lo + hi) / 2;

      if less(key, a[mid]) {
        hi := mid;
      } else if less(a[mid], key) {
        lo:= mid + 1;
      } else {
        return Some(mid);
      }
    }

    return None;
  }
}
