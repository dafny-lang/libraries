// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../Sets/Sets.dfy"
include "../../Comparison.dfy"

module Arrays{

import opened Sets
import opened Comparison
import opened Wrappers

  trait Sorter<T> {
    ghost const C := Comparison(Cmp)

    function method Cmp(t0: T, t1: T): Cmp

    twostate predicate Identical(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      reads arr
    {
      arr[lo..hi] == old(arr[lo..hi])
    }

    twostate lemma IdenticalSplit(arr: array<T>, lo: int, mid: int, hi: int)
      requires 0 <= lo <= mid <= hi <= arr.Length
      requires Identical(arr, lo, hi)
      ensures Identical(arr, lo, mid)
      ensures Identical(arr, mid, hi)
    {
      assert arr[lo..mid] == arr[lo..hi][..mid-lo];
    }

    twostate lemma IdenticalShuffled(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      requires Identical(arr, lo, hi)
      ensures Shuffled(arr, lo, hi)
    {}

    twostate predicate SameElements(arr: array<T>, lo: int, hi: int)
      reads arr
      requires 0 <= lo <= hi <= arr.Length
    {
      && Identical(arr, 0, lo)
      && Shuffled(arr, lo, hi)
      && Identical(arr, hi, arr.Length)
    }

    twostate lemma SameElementsExtend(arr: array<T>, lo: int, lo': int, hi': int, hi: int)
      requires 0 <= lo <= lo' <= hi' <= hi <= arr.Length
      requires SameElements(arr, lo', hi')
      ensures SameElements(arr, lo, hi)
    {
      assert SameElements(arr, lo', hi');
      assert Identical(arr, 0, lo') && Shuffled(arr, lo', hi') && Identical(arr, hi', arr.Length);
      IdenticalSplit(arr, 0, lo, lo'); IdenticalSplit(arr, hi', hi, arr.Length);
      assert && Identical(arr, 0, lo) && Identical(arr, lo, lo')
             && Shuffled(arr, lo', hi')
             && Identical(arr, hi', hi) && Identical(arr, hi, arr.Length);
      IdenticalShuffled(arr, lo, lo'); IdenticalShuffled(arr, hi', hi);
      assert && Identical(arr, 0, lo) && Shuffled(arr, lo, lo')
             && Shuffled(arr, lo', hi')
             && Shuffled(arr, hi', hi) && Identical(arr, hi, arr.Length);
      ShuffledConcat(arr, lo, lo', hi'); ShuffledConcat(arr, lo, hi', hi);
      assert Identical(arr, 0, lo) && Shuffled(arr, lo, hi) && Identical(arr, hi, arr.Length);
      assert SameElements(arr, lo, hi);
    }

    twostate predicate Shuffled(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      reads arr
    {
      multiset(arr[lo..hi]) == old(multiset(arr[lo..hi]))
    }
    
    predicate Sortable(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      reads arr
    {
      reveal C.Valid?(); // Leaks through
      C.Valid?(Sets.OfSlice(arr, lo, hi))
    }

    twostate lemma SetOfSliceShuffled(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      requires Shuffled(arr, lo, hi)
      ensures Sets.OfSlice(arr, lo, hi) == old(Sets.OfSlice(arr, lo, hi))
    {
      calc {
        old(Sets.OfSlice(arr, lo, hi));
        set x <- old(arr[lo..hi]);
        set x <- old(multiset(arr[lo..hi]));
        set x <- multiset(arr[lo..hi]);
        set x <- arr[lo..hi];
        Sets.OfSlice(arr, lo, hi);
      }
    }

    twostate lemma SortableSameElements(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      requires old(Sortable(arr, lo, hi))
      requires SameElements(arr, lo, hi)
      ensures Sortable(arr, lo, hi)
    {
      SetOfSliceShuffled(arr, lo, hi);
    }

    twostate lemma ShuffledConcat(arr: array<T>, lo: int, mid: int, hi: int)
      requires 0 <= lo <= mid <= hi <= arr.Length
      requires Shuffled(arr, lo, mid)
      requires Shuffled(arr, mid, hi)
      ensures Shuffled(arr, lo, hi)
    {
      calc {
        old(multiset(arr[lo..hi]));
        { assert old(arr[lo..hi] == arr[lo..mid] + arr[mid..hi]); }
        old(multiset(arr[lo..mid] + arr[mid..hi]));
        old(multiset(arr[lo..mid])) + old(multiset(arr[mid..hi]));
        multiset(arr[lo..mid]) + multiset(arr[mid..hi]);
        { assert arr[lo..hi] == arr[lo..mid] + arr[mid..hi]; }
        multiset(arr[lo..hi]);
      }
    }

    lemma Sortable_Slice(arr: array<T>, lo: int, hi: int, lo': int, hi': int)
      requires 0 <= lo <= lo' <= hi' <= hi <= arr.Length
      requires Sortable(arr, lo, hi)
      ensures Sortable(arr, lo', hi')
    {}

    predicate Sorted(arr: array<T>, lo: int, hi: int)
      reads arr
      requires 0 <= lo <= hi <= arr.Length
    {
      C.Sorted(arr[lo..hi])
    }

    lemma StripedInit(sq: seq<T>, pivot: T, lo: int, hi: int)
      requires 0 <= lo <= hi <= |sq|
      ensures C.Striped(sq, pivot, lo, lo, lo, hi, hi)
    {
      reveal C.Striped();
    }

    lemma StripedNonEmpty(sq: seq<T>, pivot: T, lo: int, left: int, mid: int, right: int, hi: int)
      requires 0 <= lo <= left <= mid <= right <= hi <= |sq|
      requires C.Striped(sq, pivot, lo, left, mid, right, hi)
      requires C.Valid?(Sets.OfSeq(sq[lo..hi]))
      requires pivot in sq[lo..hi]
      ensures left < right
    {
      reveal C.Valid?();
      var idx :| lo <= idx < hi && sq[idx] == pivot;
      C.AlwaysReflexive(pivot);
      reveal C.Striped();
    }

    twostate lemma StripedSameElements(arr: array<T>, pivot: T, lo: int, left: int, right: int, hi: int)
      requires 0 <= lo <= left <= right <= hi <= |arr[..]|
      requires Shuffled(arr, lo, left)
      requires Identical(arr, left, right)
      requires Shuffled(arr, right, hi)
      requires old(C.Striped(arr[..], pivot, lo, left, right, right, hi))
      ensures C.Striped(arr[..], pivot, lo, left, right, right, hi)
    {
      reveal C.Striped();
      forall i | lo    <= i < left ensures Cmp(arr[..][i], pivot).Lt? {
        assert arr[..][i] == arr[lo..left][i - lo];
        assert arr[..][i] in multiset(arr[lo..left]);
      }
      forall i | left  <= i < right ensures Cmp(arr[..][i], pivot).Eq? {
        assert arr[..][i] == arr[left..right][i - left];
      }
      forall i | right <= i < hi    ensures Cmp(arr[..][i], pivot).Gt? {
        assert arr[..][i] == arr[right..hi][i - right];
        assert arr[..][i] in multiset(arr[right..hi]);
      }
    }

    method Swap(arr: array<T>, ghost lo: int, i: int, j: int, ghost hi: int)
      requires 0 <= lo <= i <= j < hi <= arr.Length
      modifies arr
      ensures SameElements(arr, lo, hi)
      ensures arr[..] == old(arr[..][i := arr[j]][j := arr[i]])
    {
      arr[i], arr[j] := arr[j], arr[i];
    }

    method SwapLt(
      arr: array<T>, pivot: T,
      lo: int, left: int, mid: int, right: int, hi: int
    )
      requires 0 <= lo <= left <= mid < right <= hi <= arr.Length
      requires C.Striped(arr[..], pivot, lo, left, mid, right, hi)
      requires Cmp(arr[mid], pivot).Lt?
      modifies arr
      ensures SameElements(arr, lo, hi)
      ensures arr[..] == old(arr[..][left := arr[mid]][mid := arr[left]])
      ensures C.Striped(arr[..], pivot, lo, left + 1, mid + 1, right, hi)
    {
      reveal C.Striped();
      Swap(arr, lo, left, mid, hi);
    }

    method SwapGt(
      arr: array<T>, pivot: T,
      lo: int, left: int, mid: int, right: int, hi: int
    )
      requires 0 <= lo <= left <= mid < right <= hi <= arr.Length
      requires C.Striped(arr[..], pivot, lo, left, mid, right, hi)
      requires Cmp(arr[mid], pivot).Gt?
      modifies arr
      ensures SameElements(arr, lo, hi)
      ensures arr[..] == old(arr[..][mid := arr[right - 1]][right - 1 := arr[mid]])
      ensures C.Striped(arr[..], pivot, lo, left, mid, right - 1, hi)
    {
      reveal C.Striped();
      Swap(arr, lo, mid, right - 1, hi);
    }

    lemma SortedStripedMiddle(arr: array<T>, pivot: T, lo: int, left: int, right: int, hi: int)
      requires 0 <= lo <= left < right <= hi <= arr.Length
      requires Sortable(arr, lo, hi)
      requires pivot in multiset(arr[lo..hi])
      requires C.Striped(arr[..], pivot, lo, left, right, right, hi)
      ensures Sorted(arr, left, right)
    {
      reveal C.Striped();
      forall i, j | left  <= i < j < right ensures Cmp(arr[i], arr[j]).Le? {
        var idx :| lo <= idx < hi && arr[idx] == pivot;
        assert Cmp(arr[i], pivot) == Eq;
        assert C.Complete??(arr[j], pivot);
        assert C.Transitive??(arr[i], pivot, arr[j]);
      }
    }

    lemma SortedConcat(arr: array<T>, lo: int, mid: int, hi: int)
      requires 0 <= lo <= mid <= hi <= arr.Length
      requires Sorted(arr, lo, mid)
      requires Sorted(arr, mid, hi)
      requires forall i, j | lo <= i < mid <= j < hi :: Cmp(arr[i], arr[j]).Le?
      ensures Sorted(arr, lo, hi)
    {
      assert arr[lo..mid] + arr[mid..hi] == arr[lo..hi];
      C.SortedConcat(arr[lo..mid], arr[mid..hi]);
    }

    twostate lemma SortedIdentical(arr: array<T>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      requires old(Sorted(arr, lo, hi))
      requires Identical(arr, lo, hi)
      ensures Sorted(arr, lo, hi)
    {
      assert arr[lo..hi] == old(arr[lo..hi]);
      forall i, j | lo <= i < j < hi ensures Cmp(arr[i], arr[j]).Le? {
        assert arr[i] == arr[lo..hi][i - lo];
        assert arr[j] == arr[lo..hi][j - lo];
      }
    }

    lemma SortedDutchFlag(arr: array<T>, pivot: T, lo: int, left: int, right: int, hi: int)
      requires 0 <= lo <= left < right <= hi <= arr.Length
      requires Sortable(arr, lo, hi)
      requires pivot in multiset(arr[lo..hi])
      requires Sorted(arr, lo, left)
      requires Sorted(arr, right, hi)
      requires C.Striped(arr[..], pivot, lo, left, right, right, hi)
      ensures Sorted(arr, lo, hi)
    {
      reveal C.Striped();
      forall i, j | lo <= i < left <= j < right ensures Cmp(arr[i], arr[j]).Le? {
        var idx :| lo <= idx < hi && arr[idx] == pivot;
        assert Cmp(arr[i], pivot).Le?;
        assert Cmp(arr[j], pivot).Eq?;
        assert C.Complete??(arr[j], pivot);
        assert C.Transitive??(arr[i], pivot, arr[j]);
      }
      SortedStripedMiddle(arr, pivot, lo, left, right, hi);
      SortedConcat(arr, lo, left, right);
      forall i, j | lo <= i < right <= j < hi ensures Cmp(arr[i], arr[j]).Le? {
        assert Cmp(arr[i], pivot).Le?;
        assert Cmp(arr[j], pivot).Gt?;
        assert C.Complete??(arr[i], pivot);
        assert C.Complete??(arr[j], pivot);
        assert C.Transitive??(arr[i], pivot, arr[j]);
      }
      SortedConcat(arr, lo, right, hi);
    }

    method QuickSort(arr: array<T>, lo: int := 0, hi: int := arr.Length)
      requires 0 <= lo <= hi <= arr.Length
      requires Sortable(arr, lo, hi)
      decreases hi - lo
      modifies arr
      ensures Sortable(arr, lo, hi)
      ensures Sorted(arr, lo, hi)
      ensures SameElements(arr, lo, hi)
    {
      if hi - lo > 1 {
        var pivot := MedianOfMedians(arr, lo, hi);
        var left, right := DutchFlag(arr, pivot, lo, hi);

        label left:
        SortableSameElements(arr, lo, hi);
        Sortable_Slice(arr, lo, hi, lo, left);
        StripedNonEmpty(arr[..], pivot, lo, left, right, right, hi);
        QuickSort(arr, lo, left);

        label right:
        SameElementsExtend@left(arr, lo, lo, left, hi);
        SortableSameElements(arr, lo, hi);
        Sortable_Slice(arr, lo, hi, right, hi);
        IdenticalSplit@left(arr, left, hi, arr.Length);
        IdenticalSplit@left(arr, left, right, hi);
        IdenticalShuffled@left(arr, right, hi);
        StripedSameElements@left(arr, pivot, lo, left, right, hi);
        QuickSort(arr, right, hi);

        SameElementsExtend@right(arr, lo, right, hi, hi);
        SortableSameElements(arr, lo, hi);
        IdenticalSplit@right(arr, lo, left, right);
        SortedIdentical@right(arr, lo, left);
        StripedSameElements@right(arr, pivot, lo, left, right, hi);
        SortedDutchFlag(arr, pivot, lo, left, right, hi);
      }
    }

    function method MedianOfMedians(arr: array<T>, lo: int, hi: int): (t: T)
      requires 0 <= lo < hi <= arr.Length
      reads arr
      ensures t in arr[lo..hi]
    {
      arr[lo] // TODO
    }

      method DutchFlag(arr: array<T>, pivot: T, lo: int, hi: int) returns (left: int, right: int)
      requires 0 <= lo < hi <= arr.Length
      requires pivot in multiset(arr[lo..hi])
      modifies arr
      ensures SameElements(arr, lo, hi)
      ensures lo <= left <= right <= hi
      ensures C.Striped(arr[..], pivot, lo, left, right, right, hi)
    {
      left, right := lo, hi;
      var mid := lo;
      StripedInit(arr[..], pivot, lo, hi);

      while mid < right
        invariant pivot in multiset(arr[lo..hi])
        invariant lo <= left <= mid <= right <= hi
        invariant SameElements(arr, lo, hi)
        invariant C.Striped(arr[..], pivot, lo, left, mid, right, hi)
      {
        reveal C.Striped();
        match Cmp(arr[mid], pivot) {
          case Lt =>
            SwapLt(arr, pivot, lo, left, mid, right, hi);
            left := left + 1;
            mid := mid + 1;
          case Gt =>
            SwapGt(arr, pivot, lo, left, mid, right, hi);
            right := right - 1;
          case Eq =>
            mid := mid + 1;
        }
      }

    }
}
}