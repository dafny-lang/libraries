// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Original Copyright under the following: 
*  Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, 
*  ETH Zurich, and University of Washington
*  SPDX-License-Identifier: BSD-2-Clause 
* 
*  Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT 
* 
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../Wrappers.dfy"
include "../../Math.dfy"

module Seq {

  import opened Wrappers
  import Math

  /**********************************************************
  *
  *  Manipulating the End of a Sequence
  *
  ***********************************************************/

  /* Returns the first element of a non-empty sequence. */
  function method First<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[0]
  }

  /* Returns the subsequence of a non-empty sequence, one obtains from 
     dropping the first element. */
  function method DropFirst<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
  {
    xs[1..]
  }

  /* Returns the last element of a non-empty sequence. */
  function method Last<T>(xs: seq<T>): T
    requires |xs| > 0;
  {
    xs[|xs|-1]
  }

  /* Returns the subsequence of a non-empty sequence, one obtains from 
     dropping the last element. */
  function method DropLast<T>(xs: seq<T>): seq<T> 
    requires |xs| > 0;
  {
    xs[..|xs|-1]
  }

  /* Proves that concatenating two subsequences of a non-empty sequence, the first obtained 
     from dropping the last element, the second consisting only of the last 
     element, results in the original sequence. */
  lemma LemmaLast<T>(xs: seq<T>)
    requires |xs| > 0;
    ensures DropLast(xs) + [Last(xs)] == xs;
  {
  }

  /* Proves that the last element of two concatenated sequences, the second one being non-empty, will be the 
     last element of the latter sequence. */
  lemma LemmaAppendLast<T>(xs: seq<T>, ys: seq<T>)
    requires 0 < |ys|
    ensures Last(xs + ys) == Last(ys)
  {
  }

  /* Proves that the concatenation of sequences is associative. */
  lemma LemmaConcatIsAssociative<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
    ensures xs + (ys + zs) == (xs + ys) + zs;
  {
  }

  /**********************************************************
  *
  *  Manipulating the Content of a Sequence
  *
  ***********************************************************/
  
  /* Is true if the sequence xs is a prefix of the sequence ys. */
  predicate IsPrefix<T>(xs: seq<T>, ys: seq<T>)
    ensures IsPrefix(xs, ys) ==> (|xs| <= |ys| && xs == ys[..|xs|])
  {
    xs <= ys    
  }
  
  /* Is true if the sequence xs is a suffix of the sequence ys. */
  predicate IsSuffix<T>(xs: seq<T>, ys: seq<T>)
  {
    && |xs| <= |ys|
    && xs == ys[|ys|-|xs|..]
  }

  /* Proves that a sequence that is sliced at the pos-th element, concatenated 
     with that same sequence sliced from the pos-th element, is equal to the 
     original unsliced sequence. */
  lemma LemmaSplitAt<T>(xs: seq<T>, pos: nat)
    requires pos < |xs|;
    ensures xs[..pos] + xs[pos..] == xs;
  {
  }

  /* Proves that any element in a slice is included in the original sequence. */
  lemma LemmaElementFromSlice<T>(xs: seq<T>, ys:seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= b <= |xs|;
    requires ys == xs[a..b];
    requires a <= pos < b;
    ensures  pos - a < |ys|;
    ensures  ys[pos-a] == xs[pos];
  {
  }

  lemma LemmaSliceOfSlice<T>(xs: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |xs|;
    requires 0 <= s2 <= e2 <= e1 - s1;
    ensures  xs[s1..e1][s2..e2] == xs[s1+s2..s1+e2];
  {
    var r1 := xs[s1..e1];
    var r2 := r1[s2..e2];
    var r3 := xs[s1+s2..s1+e2];
    assert |r2| == |r3|;
    forall i {:trigger r2[i], r3[i]}| 0 <= i < |r2| ensures r2[i] == r3[i];
    {
    }
  }

  /* Converts a sequence to an array. */
  method ToArray<T>(xs: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |xs|
    ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
  {
    a := new T[|xs|](i requires 0 <= i < |xs| => xs[i]);
  }

  /* Converts a sequence to a set. */
  function method {:opaque} ToSet<T>(xs: seq<T>): set<T> 
  {
    set x: T | x in xs
  }

  /* Proves that the cardinality of a subsequence is always less than or 
     equal to that of the full sequence. */
  lemma LemmaCardinalityOfSet<T>(xs: seq<T>)
    ensures |ToSet(xs)| <= |xs| 
  {
    reveal ToSet();
    if |xs| == 0 {
    } else {
      assert ToSet(xs) == ToSet(DropLast(xs)) + {Last(xs)};
      LemmaCardinalityOfSet(DropLast(xs));
    }
  }
  
  /* Proves that a sequence is of length 0 if and only if its conversion to
     a set results in the empty set. */
  lemma LemmaCardinalityOfEmptySetIs0<T>(xs: seq<T>)
    ensures |ToSet(xs)| == 0 <==> |xs| == 0
  {
    reveal ToSet();
    if |xs| != 0 {
      assert xs[0] in ToSet(xs);
    }
  }

  /* Is true if there are no duplicate values in the sequence. */
  predicate {:opaque} HasNoDuplicates<T>(xs: seq<T>) 
  {
    (forall i, j {:trigger xs[i], xs[j]}:: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j])
  }

  /* Proves that if sequences xs and ys don't have duplicates and there are no 
     elements in common between them, then the concatenated sequence xs + ys 
     will not contain duplicates either. */
  lemma {:timeLimitMultiplier 3} LemmaNoDuplicatesInConcat<T>(xs: seq<T>, ys: seq<T>)
    requires HasNoDuplicates(xs);
    requires HasNoDuplicates(ys);
    requires multiset(xs) !! multiset(ys);
    ensures HasNoDuplicates(xs+ys);
  {
    reveal HasNoDuplicates();
    var zs := xs + ys;
    if |zs| > 1 {
      assert forall i, j {:trigger zs[i], zs[j]}:: i != j && 0 <= i < |xs| && |xs| <= j < |zs| ==>
        zs[i] in multiset(xs) && zs[j] in multiset(ys) && zs[i] != zs[j]; 
    }
  }

  /* Proves that a sequence with no duplicates converts to a set of the same 
     cardinality. */
  lemma LemmaCardinalityOfSetNoDuplicates<T>(xs: seq<T>)
    requires HasNoDuplicates(xs)
    ensures |ToSet(xs)| == |xs|
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if |xs| == 0 {
    } else {
      LemmaCardinalityOfSetNoDuplicates(DropLast(xs));
      assert ToSet(xs) == ToSet(DropLast(xs)) + {Last(xs)};
    }
  }

  /* Proves that a sequence with cardinality equal to its set has no duplicates. */
  lemma LemmaNoDuplicatesCardinalityOfSet<T>(xs: seq<T>)
    requires |ToSet(xs)| == |xs|
    ensures HasNoDuplicates(xs)
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if |xs| == 0 {
    } else {
      assert xs == [First(xs)] + DropFirst(xs);
      assert ToSet(xs) == {First(xs)} + ToSet(DropFirst(xs));
      if First(xs) in DropFirst(xs) {
        // If there is a duplicate, then we show that |ToSet(s)| == |s| cannot hold.
        assert ToSet(xs) == ToSet(DropFirst(xs));
        LemmaCardinalityOfSet(DropFirst(xs));
        assert |ToSet(xs)| <= |DropFirst(xs)|;
      } else {
        assert |ToSet(xs)| == 1 + |ToSet(DropFirst(xs))|;
        LemmaNoDuplicatesCardinalityOfSet(DropFirst(xs));
      }
    }
  }

  /* Proves that if a sequence has no duplicates, then each element occurs only 
     once in its conversion to a multiset. */
  lemma LemmaMultisetHasNoDuplicates<T>(xs: seq<T>)
    requires HasNoDuplicates(xs)
    ensures forall x {:trigger multiset(xs)[x]} | x in multiset(xs):: multiset(xs)[x] == 1
  {
    if |xs| == 0 {
    } else {
      assert xs == DropLast(xs) + [Last(xs)];
      assert Last(xs) !in DropLast(xs) by {
        reveal HasNoDuplicates();
      }
      assert HasNoDuplicates(DropLast(xs)) by {
        reveal HasNoDuplicates();
      }
      LemmaMultisetHasNoDuplicates(DropLast(xs));
    }
  }

  /* If an element occurs at least once in a sequence, the index of its
     first occurance is returned. */
  function method {:opaque} IndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j {:trigger xs[j]} :: 0 <= j < i ==> xs[j] != v
  {
    if xs[0] == v then 0 else 1 + IndexOf(xs[1..], v)
  }

  /* Returns Some i, if an element occurs at least once in a sequence, and i is 
     the index of its first occurance. Otherwise the return is None. */
  function method {:opaque} IndexOfOption<T(==)>(xs: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && xs[o.value] == v &&
                            forall j {:trigger xs[j]} :: 0 <= j < o.value ==> xs[j] != v
            else v !in xs
  {
    if |xs| == 0 then None()
    else
      if xs[0] == v then Some(0)
      else
        var o' := IndexOfOption(xs[1..], v);
        if o'.Some? then Some(o'.value + 1) else None()
  }

  /* If an element occurs at least once in a sequence, the index of its
     last occurance is returned. */
  function method {:opaque} LastIndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j {:trigger xs[j]} :: i < j < |xs| ==> xs[j] != v
  {
    if xs[|xs|-1] == v then |xs| - 1 else LastIndexOf(xs[..|xs|-1], v)
  }

  /* Returns Some i, if an element occurs at least once in a sequence, and i is 
     the index of its last occurance. Otherwise the return is None. */
  function method {:opaque} LastIndexOfOption<T(==)>(xs: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && xs[o.value] == v &&
                            forall j {:trigger xs[j]} :: o.value < j < |xs| ==> xs[j] != v
            else v !in xs
  {
    if |xs| == 0 then None()
    else if xs[|xs|-1] == v then Some(|xs| - 1) else LastIndexOfOption(xs[..|xs|-1], v)
  }

  /* Returns a sequence without the element at a given position. */
  function method {:opaque} Remove<T>(xs: seq<T>, pos: nat): (ys: seq<T>)
    requires pos < |xs|
    ensures |ys| == |xs| - 1
    ensures forall i {:trigger ys[i], xs[i]} | 0 <= i < pos :: ys[i] == xs[i]
    ensures forall i {:trigger ys[i]} | pos <= i < |xs| - 1 :: ys[i] == xs[i+1]
  {
    xs[..pos] + xs[pos+1..]
  }

  /* If a given element occurs at least once in a sequence, the sequence without
     its first occurance is returned. Otherwise the same sequence is returned. */
  function method {:opaque} RemoveValue<T(==)>(xs: seq<T>, v: T): (ys: seq<T>)
    ensures v !in xs ==> xs == ys
    ensures v in xs ==> |multiset(ys)| == |multiset(xs)| - 1
    ensures v in xs ==> multiset(ys)[v] == multiset(xs)[v] - 1
    ensures HasNoDuplicates(xs) ==> HasNoDuplicates(ys) && ToSet(ys) == ToSet(xs) - {v}
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if v !in xs then xs
    else
      var i := IndexOf(xs, v);
      assert xs == xs[..i] + [v] + xs[i+1..];
      xs[..i] + xs[i+1..]
  }

  /* Inserts an element at a given position and returns the resulting sequence. */
  function method {:opaque} Insert<T>(xs: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |xs|
    ensures |Insert(xs, a, pos)| == |xs| + 1
    ensures forall i {:trigger Insert(xs, a, pos)[i], xs[i]} :: 0 <= i < pos ==> Insert(xs, a, pos)[i] == xs[i]
    ensures forall i {:trigger xs[i]} :: pos <= i < |xs| ==> Insert(xs, a, pos)[i+1] == xs[i]
    ensures Insert(xs, a, pos)[pos] == a
    ensures multiset(Insert(xs, a, pos)) == multiset(xs) + multiset{a}
  {
    assert xs == xs[..pos] + xs[pos..];
    xs[..pos] + [a] + xs[pos..]
  }

  /* Returns the sequence that is in reverse order to a given sequence. */
  function method {:opaque} Reverse<T>(xs: seq<T>): (ys: seq<T>)
    ensures |ys| == |xs|
    ensures forall i {:trigger ys[i]}{:trigger xs[|xs| - i - 1]} :: 0 <= i < |xs| ==> ys[i] == xs[|xs| - i - 1]
  {
    if xs == [] then [] else [xs[|xs|-1]] + Reverse(xs[0 .. |xs|-1])
  }
    
  /* Returns a constant sequence of a given length. */
  function method {:opaque} Repeat<T>(v: T, length: nat): (xs: seq<T>)
    ensures |xs| == length
    ensures forall i: nat {:trigger xs[i]} | i < |xs| :: xs[i] == v
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }
  
  /* Unzips a sequence that contains pairs into two seperate sequences. */
  function method {:opaque} Unzip<A,B>(xs: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(xs).0| == |Unzip(xs).1| == |xs|
    ensures forall i {:trigger Unzip(xs).0[i]} {:trigger Unzip(xs).1[i]} 
        :: 0 <= i < |xs| ==> (Unzip(xs).0[i], Unzip(xs).1[i]) == xs[i]
  {
    if |xs| == 0 then ([], [])
    else
      var (a, b):= Unzip(DropLast(xs));
      (a + [Last(xs).0], b + [Last(xs).1])
  }

  /* Zips two sequences into one sequence that consists of pairs. */
  function method {:opaque} Zip<A,B>(xs: seq<A>, ys: seq<B>): seq<(A, B)>
    requires |xs| == |ys|
    ensures |Zip(xs, ys)| == |xs|
    ensures forall i {:trigger Zip(xs, ys)[i]}:: 0 <= i < |Zip(xs, ys)| ==> Zip(xs, ys)[i] == (xs[i], ys[i])
    ensures Unzip(Zip(xs, ys)).0 == xs
    ensures Unzip(Zip(xs, ys)).1 == ys
  {
    if |xs| == 0 then []
    else Zip(DropLast(xs), DropLast(ys)) + [(Last(xs), Last(ys))]
  }

  /* Proves that if a sequence is unzipped and then zipped, the original sequence 
     is recovered. */
  lemma LemmaZipOfUnzip<A,B>(xs: seq<(A,B)>)
    ensures Zip(Unzip(xs).0, Unzip(xs).1) == xs
  {
  }

  /**********************************************************
  *
  *  Extrema in Sequences
  *
  ***********************************************************/

  /* Returns the maximum integer value in a non-empty sequence of integers. */
  function method {:opaque} Max(xs: seq<int>): int
    requires 0 < |xs|
    ensures forall k {:trigger k in xs} :: k in xs ==> Max(xs) >= k
    ensures Max(xs) in xs
  {
    assert xs == [xs[0]] + xs[1..];
    if |xs| == 1 then xs[0] else Math.Max(xs[0], Max(xs[1..]))
  }

  /* Proves that the maximum of the concatenation of two non-empty sequences is 
     greater or equal than the maxima of its two non-empty subsequences. */
  lemma LemmaMaxOfConcat(xs: seq<int>, ys: seq<int>)
    requires 0 < |xs| && 0 < |ys|
    ensures Max(xs+ys) >= Max(xs)
    ensures Max(xs+ys) >= Max(ys)
    ensures forall i {:trigger i in [Max(xs + ys)]} :: i in xs + ys ==> Max(xs + ys) >= i
  {
    reveal Max();
    if |xs| == 1 {
    } else {
      assert xs[1..] + ys == (xs + ys)[1..];
      LemmaMaxOfConcat(xs[1..], ys);
    }
  }

  /* Returns the minimum integer value in a non-empty sequence of integers. */
  function method {:opaque} Min(xs: seq<int>): int
    requires 0 < |xs|
    ensures forall k {:trigger k in xs} :: k in xs ==> Min(xs) <= k
    ensures Min(xs) in xs
  {
    assert xs == [xs[0]] + xs[1..];
    if |xs| == 1 then xs[0] else Math.Min(xs[0], Min(xs[1..]))
  }

  /* Proves that minimum of the concatenation of two non-empty sequences is 
     less or equal than the minima of its two non-empty subsequences. */
  lemma LemmaMinOfConcat(xs: seq<int>, ys: seq<int>)
    requires 0 < |xs| && 0 < |ys|
    ensures Min(xs+ys) <= Min(xs)
    ensures Min(xs+ys) <= Min(ys)
    ensures forall i {:trigger i in xs + ys} :: i in xs + ys ==> Min(xs + ys) <= i
  {
    reveal Min();
    if |xs| == 1 {
    } else {
      assert xs[1..] + ys == (xs + ys)[1..];
      LemmaMinOfConcat(xs[1..], ys);
    }
  }

  /* Proves that the maximum element in a non-empty sequence is greater or equal 
     than the maxima of its non-empty subsequences. */
  lemma LemmaSubseqMax(xs: seq<int>, from: nat, to: nat)
    requires from < to <= |xs|
    ensures Max(xs[from..to]) <= Max(xs)
  {
    var subseq := xs[from..to];
    if Max(subseq) > Max(xs) {
      var k :| 0 <= k < |subseq| && subseq[k] == Max(subseq);
      assert xs[seq(|subseq|, i requires 0 <= i < |subseq| => i + from)[k]] in xs;
      assert false;
    }
  }

  /* Proves that the minimum element in a non-empty sequence is less or equal 
     than the minima of its non-empty subsequences. */
  lemma LemmaSubseqMin(xs: seq<int>, from: nat, to: nat)
    requires from < to <= |xs|
    ensures Min(xs[from..to]) >= Min(xs)
  {
    var subseq := xs[from..to];
    if Min(subseq) < Min(xs) {
      var k :| 0 <= k < |subseq| && subseq[k] == Min(subseq);
      assert xs[seq(|subseq|, i requires 0 <= i < |subseq| => i + from)[k]] in xs;
    }
  }

  /**********************************************************
  *
  *  Sequences of Sequences
  *
  ***********************************************************/

  /* Flattens a sequence of sequences into a single sequence by concatenating 
     subsequences, starting from the first element. */
  function method Flatten<T>(xs: seq<seq<T>>): seq<T>
    decreases |xs|
  {
    if |xs| == 0 then []
    else xs[0] + Flatten(xs[1..])
  }

  /* Proves that flattening sequences of sequences is additive. That is, concatenating
     the flattening of two sequences of sequences is the same as flattening the 
     concatenation of two sequences of sequences. */
  lemma LemmaFlattenConcat<T>(xs: seq<seq<T>>, ys: seq<seq<T>>)
    ensures Flatten(xs + ys) == Flatten(xs) + Flatten(ys)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc == {
        Flatten(xs + ys);
          { assert (xs + ys)[0] == xs[0];  assert (xs + ys)[1..] == xs[1..] + ys; }
        xs[0] + Flatten(xs[1..] + ys);
        xs[0] + Flatten(xs[1..]) + Flatten(ys);
        Flatten(xs) + Flatten(ys);
      }
    }
  }

  /* Flattens a sequence of sequences into a single sequence by concatenating 
     subsequences in reverse order, i.e. starting from the last element. */
  function method FlattenReverse<T>(xs: seq<seq<T>>): seq<T>
    decreases |xs|
  {
    if |xs| == 0 then []
    else FlattenReverse(DropLast(xs)) + Last(xs)
  }

  /* Proves that flattening sequences of sequences in reverse order is additive. 
     That is, concatenating the flattening of two sequences of sequences in reverse 
     order is the same as flattening the concatenation of two sequences of sequences
     in reverse order. */
  lemma LemmaFlattenReverseConcat<T>(xs: seq<seq<T>>, ys: seq<seq<T>>)
    ensures FlattenReverse(xs + ys) == FlattenReverse(xs) + FlattenReverse(ys)
  {
    if |ys| == 0 {
      assert FlattenReverse(ys) == [];
      assert xs + ys == xs;
    } else {
      calc == {
        FlattenReverse(xs + ys);
          { assert Last(xs + ys) == Last(ys);  assert DropLast(xs + ys) == xs + DropLast(ys); }
        FlattenReverse(xs + DropLast(ys)) + Last(ys);
        FlattenReverse(xs) + FlattenReverse(DropLast(ys)) + Last(ys);
        FlattenReverse(xs) + FlattenReverse(ys);
      }
    }
  }

  /* Proves that flattening sequences of sequences in order (starting from the front)
     and in reverse order (starting from the back) results in the same sequence. */
  lemma LemmaFlattenAndFlattenReverseAreEquivalent<T>(xs: seq<seq<T>>)
    ensures Flatten(xs) == FlattenReverse(xs)
  {
    if |xs| == 0 {
    } else {
      calc == {
        FlattenReverse(xs);
        FlattenReverse(DropLast(xs)) + Last(xs);
          { LemmaFlattenAndFlattenReverseAreEquivalent(DropLast(xs)); }
        Flatten(DropLast(xs)) + Last(xs);
        Flatten(DropLast(xs)) + Flatten([Last(xs)]);
          { LemmaFlattenConcat(DropLast(xs), [Last(xs)]); 
        assert xs == DropLast(xs) + [Last(xs)]; }
        Flatten(xs);
      }
    }
  }

  /* Proves that the length of a flattened sequence of sequences xs is greater or 
     equal than any of the lengths of the elements of xs.  */
  lemma LemmaFlattenLengthGeSingleElementLength<T>(xs: seq<seq<T>>, i: int)
    requires 0 <= i < |xs|
    ensures |FlattenReverse(xs)| >= |xs[i]|
  {
    if i < |xs| - 1 {
      LemmaFlattenLengthGeSingleElementLength(xs[..|xs|-1], i);
    }
  }

  /* Proves that the length of a flattened sequence of sequences xs is less or equal 
     than the length of xs multiplied by a number not smaller than the length of the 
     longest sequence in xs. */
  lemma LemmaFlattenLengthLeMul<T>(xs: seq<seq<T>>, j: int)
    requires forall i {:trigger xs[i]} | 0 <= i < |xs| :: |xs[i]| <= j
    ensures |FlattenReverse(xs)| <= |xs| * j
  {
    if |xs| == 0 {
    } else {
      LemmaFlattenLengthLeMul(xs[..|xs|-1], j);
      assert |FlattenReverse(xs[..|xs|-1])| <= (|xs|-1) * j;
    }
  }


  /**********************************************************
  *
  *  Higher-Order Sequence Functions
  *
  ***********************************************************/

  /* Returns the sequence one obtains from applying a function to every element 
     of a sequence. */
  function method {:opaque} Map<T,R>(f: (T ~> R), xs: seq<T>): (result: seq<R>)
    requires forall i {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| == |xs|
    ensures forall i {:trigger result[i]}:: 0 <= i < |xs| ==> result[i] == f(xs[i]);
    reads set i, o {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]):: o
  {
    if |xs| == 0 then []
    else [f(xs[0])] + Map(f, xs[1..])
  }

/* Applies to every element of a sequence a function that is either successful, or
   returns an error. Returns either an error, or, if successful at every element, the
   transformed sequence.  */
  function method {:opaque} MapWithResult<T, R, E>(f: (T ~> Result<R,E>), xs: seq<T>): (result: Result<seq<R>, E>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures result.Success? ==>
      && |result.value| == |xs|
      && (forall i :: 0 <= i < |xs| ==> 
        && f(xs[i]).Success?
        && result.value[i] == f(xs[i]).value)
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then Success([])
    else
      var head :- f(xs[0]);
      var tail :- MapWithResult(f, xs[1..]);
      Success([head] + tail)
  }

  /* Proves that applying a function to a sequence is additive. That is, concatenating 
     two sequences and then applying Map is the same as applying Map on each sequence 
     seperately, and then concatenating the two resulting sequences. */
  lemma {:opaque} LemmaMapDistributesOverConcat<T,R>(f: (T ~> R), xs: seq<T>, ys: seq<T>)
    requires forall i {:trigger xs[i]}:: 0 <= i < |xs| ==> f.requires(xs[i])
    requires forall j {:trigger ys[j]}:: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures Map(f, xs + ys) == Map(f, xs) + Map(f, ys)
  {
    reveal Map();
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        Map(f, xs + ys);
          { assert (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys; }
        Map(f, [xs[0]]) + Map(f, xs[1..] + ys);
        Map(f, [xs[0]]) + Map(f, xs[1..]) + Map(f, ys);
          {assert [(xs + ys)[0]] + xs[1..] + ys == xs + ys;}
        Map(f, xs) + Map(f, ys);
      }
    }
  }

  /* Returns the subsequence of those elements of a sequence that satisfy a given 
     predicate. */
  function method {:opaque} Filter<T>(f: (T ~> bool), xs: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| <= |xs|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |xs| == 0 then []
    else (if f(xs[0]) then [xs[0]] else []) + Filter(f, xs[1..])
  }

  /* Proves that filtering a sequence is additive. That is, concatenating two sequences 
     and then using "Filter" is the same as using "Filter" on each sequence seperately, 
     and then concatenating the two resulting sequences. */
  lemma {:opaque} LemmaFilterDistributesOverConcat<T>(f: (T ~> bool), xs: seq<T>, ys: seq<T>)
    requires forall i {:trigger xs[i]}:: 0 <= i < |xs| ==> f.requires(xs[i])
    requires forall j {:trigger ys[j]}:: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures Filter(f, xs + ys) == Filter(f, xs) + Filter(f, ys)
  {
    reveal Filter();
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        Filter(f, xs + ys);
          { assert (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys; }
        Filter(f, [xs[0]]) + Filter(f, xs[1..] + ys);
        Filter(f, [xs[0]]) + Filter(f, xs[1..]) + Filter(f, ys);
          { assert [(xs + ys)[0]] + xs[1..] + ys == xs + ys; }
        Filter(f, xs) + Filter(f, ys);
      }
    }
  }
  
  /* Folds a sequence xs to the left, by acting on the initial element init via the 
     function f. */
  function method {:opaque} FoldLeft<A,T>(f: (A, T) -> A, init: A, xs: seq<T>): A
  {
    if |xs| == 0 then init
    else FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  /* Proves that folding to the left is additive. That is, concatenating two sequences 
     and then folding them to the left, is the same as folding to the left the first 
     sequence and using the result to fold to the left the second sequence. */
  lemma {:opaque} LemmaFoldLeftDistributesOverConcat<A,T>(f: (A, T) -> A, init: A, xs: seq<T>, ys: seq<T>)
    requires 0 <= |xs + ys|
    ensures FoldLeft(f, init, xs + ys) == FoldLeft(f, FoldLeft(f, init, xs), ys)
  {
    reveal FoldLeft();
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      assert |xs| >= 1;
      assert ([xs[0]] + xs[1..] + ys)[0] == xs[0];
      calc {
        FoldLeft(f, FoldLeft(f, init, xs), ys);
        FoldLeft(f, FoldLeft(f, f(init, xs[0]), xs[1..]), ys);
          { LemmaFoldLeftDistributesOverConcat(f, f(init, xs[0]), xs[1..], ys); }
        FoldLeft(f, f(init, xs[0]), xs[1..] + ys);
          { assert (xs + ys)[0] == xs[0];
            assert (xs + ys)[1..] == xs[1..] + ys; }
        FoldLeft(f, init, xs + ys);
      }
    }
  }

  /* Is true, if inv is an invariant under stp, which is a relational 
     version of the function f passed to fold. */
  predicate InvFoldLeft<A(!new),B(!new)>(inv: (B, seq<A>) -> bool,
                                         stp: (B, A, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B ::
      inv(b, [x] + xs) && stp(b, x, b') ==> inv(b', xs)
  }

  /* inv(b, xs) ==> inv(FoldLeft(f, b, xs), []). */
  lemma LemmaInvFoldLeft<A,B>(inv: (B, seq<A>) -> bool,
                              stp: (B, A, B) -> bool,
                              f: (B, A) -> B,
                              b: B,
                              xs: seq<A>)
    requires InvFoldLeft(inv, stp)
    requires forall b, a :: stp(b, a, f(b, a))
    requires inv(b, xs)
    ensures inv(FoldLeft(f, b, xs), [])
  {
    reveal FoldLeft();
    if xs == [] {
    } else {
      assert [xs[0]] + xs[1..] == xs;
      LemmaInvFoldLeft(inv, stp, f, f(b, xs[0]), xs[1..]);
    }
  }

  /* Folds a sequence xs to the right, by acting on the initial element init via the 
     function f. */
  function method {:opaque} FoldRight<A,T>(f: (T, A) -> A, xs: seq<T>, init: A): A
  {
    if |xs| == 0 then init
    else f(xs[0], FoldRight(f, xs[1..], init))
  }

  /* Proves that folding to the right is (contravariant) additive. That is, concatenating
     two sequences and then folding them to the right, is the same as folding to the right 
     the second sequence and using the result to fold to the right the first sequence. */
  lemma {:opaque} LemmaFoldRightDistributesOverConcat<A,T>(f: (T, A) -> A, init: A, xs: seq<T>, ys: seq<T>)
    requires 0 <= |xs + ys|
    ensures FoldRight(f, xs + ys, init) == FoldRight(f, xs, FoldRight(f, ys, init))
  {
    reveal FoldRight();
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        FoldRight(f, xs, FoldRight(f, ys, init));
        f(xs[0], FoldRight(f, xs[1..], FoldRight(f, ys, init)));
        f(xs[0], FoldRight(f, xs[1..] + ys, init));
          { assert (xs + ys)[0] == xs[0];
            assert (xs +ys)[1..] == xs[1..] + ys; }
        FoldRight(f, xs + ys, init);
      }
    }
  }

  /* Is true, if inv is an invariant under stp, which is a relational version
     of the function f passed to fold. */
  predicate InvFoldRight<A(!new),B(!new)>(inv: (seq<A>, B) -> bool,
                                          stp: (A, B, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B ::
      inv(xs, b) && stp(x, b, b') ==> inv(([x] + xs), b')
  }

  /* inv([], b) ==> inv(xs, FoldRight(f, xs, b)) */
  lemma LemmaInvFoldRight<A,B>(inv: (seq<A>, B) -> bool,
                               stp: (A, B, B) -> bool,
                               f: (A, B) -> B,
                               b: B,
                               xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a, b :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
  {
    reveal FoldRight();
    if xs == [] {
    } else {
      assert [xs[0]] + xs[1..] == xs;
    }
  }

}
