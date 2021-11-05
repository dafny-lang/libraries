// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

  /* finds the first element in the sequence */
  function method First<T>(s: seq<T>): T
    requires |s| > 0
  {
    s[0]
  }

  function method DropFirst<T>(s: seq<T>): seq<T>
    requires |s| > 0
  {
    s[1..]
  }

  /* finds the last element in the sequence */
  function method Last<T>(s: seq<T>): T
    requires |s| > 0;
  {
    s[|s|-1]
  }

  /* returns the sequence slice up to but not including the last element */
  function method DropLast<T>(s: seq<T>): seq<T> 
    requires |s| > 0;
  {
    s[..|s|-1]
  }

  /* concatenating everything but the last element + the last element results in the original seq */
  lemma LemmaLast<T>(s: seq<T>)
    requires |s| > 0;
    ensures  DropLast(s) + [Last(s)] == s;
  {
  }

  /* the last element in an appended sequence will be the last element of the latter sequence */
  lemma LemmaAppendLast<T>(a: seq<T>, b: seq<T>)
    requires 0 < |a + b| && 0 < |b|
    ensures Last(a + b) == Last(b)
  {
  }

  /* explains associative property of sequences in addition */
  lemma LemmaConcatIsAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == (a + b) + c;
  {
  }

  /**********************************************************
  *
  *  Manipulating the Content of a Sequence
  *
  ***********************************************************/
  
  predicate IsPrefix<T>(a: seq<T>, b: seq<T>)
    ensures IsPrefix(a, b) ==> (|a| <= |b| && a == b[..|a|])
  {
    a <= b    
  }
  
  predicate IsSuffix<T>(a: seq<T>, b: seq<T>)
  {
    && |a| <= |b|
    && a == b[|b|-|a|..]
  }

  /* a sequence that is sliced at the jth element concatenated with that same
  sequence sliced from the jth element is equal to the original, unsliced sequence */
  lemma LemmaSplitAt<T>(s: seq<T>, pos: nat)
    requires pos < |s|;
    ensures s[..pos] + s[pos..] == s;
  {
  }

  /* ensures that the element from a slice is included in the original sequence */
  lemma LemmaElementFromSlice<T>(s: seq<T>, s':seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= b <= |s|;
    requires s' == s[a..b];
    requires a <= pos < b;
    ensures  pos - a < |s'|;
    ensures  s'[pos-a] == s[pos];
  {
  }

  lemma LemmaSliceOfSlice<T>(s: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |s|;
    requires 0 <= s2 <= e2 <= e1 - s1;
    ensures  s[s1..e1][s2..e2] == s[s1+s2..s1+e2];
  {
    var r1 := s[s1..e1];
    var r2 := r1[s2..e2];
    var r3 := s[s1+s2..s1+e2];
    assert |r2| == |r3|;
    forall i {:trigger r2[i], r3[i]}| 0 <= i < |r2| ensures r2[i] == r3[i];
    {
    }
  }

  /* converts a sequence to an array */
  method ToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }

  /* converts a sequence to a set */
  function method {:opaque} ToSet<T>(s: seq<T>): set<T> 
  {
    set x: T | x in s
  }

  /* proves that the cardinality of a subsequence is always less than or equal to that
  of the full sequence */
  lemma LemmaCardinalityOfSet<T>(s: seq<T>)
    ensures |ToSet(s)| <= |s| 
  {
    reveal ToSet();
    if |s| == 0 {
    } else {
      assert ToSet(s) == ToSet(DropLast(s)) + {Last(s)};
      LemmaCardinalityOfSet(DropLast(s));
    }
  }
  
  /* the cardinality of a subsequence of an empty sequence is also 0 */
  lemma LemmaCardinalityOfEmptySetIs0<T>(s: seq<T>)
    ensures |ToSet(s)| == 0 <==> |s| == 0
  {
    reveal ToSet();
    if |s| != 0 {
      assert s[0] in ToSet(s);
    }
  }

  /* is true if there are no duplicate values in the sequence */
  predicate {:opaque} HasNoDuplicates<T>(s: seq<T>) 
  {
    (forall i, j {:trigger s[i], s[j]}:: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j])
  }

  /* if sequence a and b don't have duplicates and there are no elements in
  common between them, then the concatenated sequence of a + b will not contain
  duplicates either */
  lemma {:timeLimitMultiplier 3} LemmaNoDuplicatesInConcat<T>(a: seq<T>, b: seq<T>)
    requires HasNoDuplicates(a);
    requires HasNoDuplicates(b);
    requires multiset(a) !! multiset(b);
    ensures HasNoDuplicates(a+b);
  {
    reveal HasNoDuplicates();
    var c := a + b;
    if |c| > 1 {
      assert forall i, j {:trigger c[i], c[j]}:: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; 
    }
  }

  /* A sequence with no duplicates converts to a set of the same cardinality */
  lemma LemmaCardinalityOfSetNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures |ToSet(s)| == |s|
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if |s| == 0 {
    } else {
      LemmaCardinalityOfSetNoDuplicates(DropLast(s));
      assert ToSet(s) == ToSet(DropLast(s)) + {Last(s)};
    }
  }

  /* A sequence with cardinality equal to its set has no duplicates */
  lemma LemmaNoDuplicatesCardinalityOfSet<T>(s: seq<T>)
    requires |ToSet(s)| == |s|
    ensures HasNoDuplicates(s)
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if |s| == 0 {
    } else {
      assert s == [First(s)] + DropFirst(s);
      assert ToSet(s) == {First(s)} + ToSet(DropFirst(s));
      if First(s) in DropFirst(s) {
        // If there is a duplicate, then we show that |ToSet(s)| == |s| cannot hold.
        assert ToSet(s) == ToSet(DropFirst(s));
        LemmaCardinalityOfSet(DropFirst(s));
        assert |ToSet(s)| <= |DropFirst(s)|;
      } else {
        assert |ToSet(s)| == 1 + |ToSet(DropFirst(s))|;
        LemmaNoDuplicatesCardinalityOfSet(DropFirst(s));
      }
    }
  }

  /* proves that there are no duplicate values in the multiset version of the sequence */
  lemma LemmaMultisetHasNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures forall x {:trigger multiset(s)[x]} | x in multiset(s):: multiset(s)[x] == 1
  {
    if |s| == 0 {
    } else {
      assert s == DropLast(s) + [Last(s)];
      assert Last(s) !in DropLast(s) by {
        reveal HasNoDuplicates();
      }
      assert HasNoDuplicates(DropLast(s)) by {
        reveal HasNoDuplicates();
      }
      LemmaMultisetHasNoDuplicates(DropLast(s));
    }
  }

  /* finds the index of the first occurrence of an element in the sequence */
  function method {:opaque} IndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j {:trigger s[j]} :: 0 <= j < i ==> s[j] != v
  {
    if s[0] == v then 0 else 1 + IndexOf(s[1..], v)
  }

  /* finds the index of the first occurrence of an element in the sequence if
  found */
  function method {:opaque} IndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v &&
                            forall j {:trigger s[j]} :: 0 <= j < o.value ==> s[j] != v
            else v !in s
  {
    if |s| == 0 then None()
    else
      if s[0] == v then Some(0)
      else
        var o' := IndexOfOption(s[1..], v);
        if o'.Some? then Some(o'.value + 1) else None()
  }

  /* finds the index of the last occurrence of an element in the sequence */
  function method {:opaque} LastIndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j {:trigger s[j]} :: i < j < |s| ==> s[j] != v
  {
    if s[|s|-1] == v then |s| - 1 else LastIndexOf(s[..|s|-1], v)
  }

  /* finds the index of the last occurrence of an element in the sequence if
  found */
  function method {:opaque} LastIndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v &&
                            forall j {:trigger s[j]} :: o.value < j < |s| ==> s[j] != v
            else v !in s
  {
    if |s| == 0 then None()
    else if s[|s|-1] == v then Some(|s| - 1) else LastIndexOfOption(s[..|s|-1], v)
  }

  /* slices out a specific position's value from the sequence */
  function method {:opaque} Remove<T>(s: seq<T>, pos: nat): (s': seq<T>)
    requires pos < |s|
    ensures |s'| == |s| - 1
    ensures forall i {:trigger s'[i], s[i]} | 0 <= i < pos :: s'[i] == s[i]
    ensures forall i {:trigger s'[i]} | pos <= i < |s| - 1 :: s'[i] == s[i+1]
  {
    s[..pos] + s[pos+1..]
  }

  /* slices out a specific value from the sequence */
  function method {:opaque} RemoveValue<T(==)>(s: seq<T>, v: T): (s': seq<T>)
    ensures v !in s ==> s == s'
    ensures v in s ==> |multiset(s')| == |multiset(s)| - 1
    ensures v in s ==> multiset(s')[v] == multiset(s)[v] - 1
    ensures HasNoDuplicates(s) ==> HasNoDuplicates(s') && ToSet(s') == ToSet(s) - {v}
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if v !in s then s
    else
      var i := IndexOf(s, v);
      assert s == s[..i] + [v] + s[i+1..];
      s[..i] + s[i+1..]
  }

  /* inserts a certain value into a specified index of the sequence */
  function method {:opaque} Insert<T>(s: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |s|
    ensures |Insert(s, a, pos)| == |s| + 1
    ensures forall i {:trigger Insert(s, a, pos)[i], s[i]} :: 0 <= i < pos ==> Insert(s, a, pos)[i] == s[i]
    ensures forall i {:trigger s[i]} :: pos <= i < |s| ==> Insert(s, a, pos)[i+1] == s[i]
    ensures Insert(s, a, pos)[pos] == a
    ensures multiset(Insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    assert s == s[..pos] + s[pos..];
    s[..pos] + [a] + s[pos..]
  }

  function method {:opaque} Reverse<T>(s: seq<T>): (s': seq<T>)
    ensures |s'| == |s|
    ensures forall i {:trigger s'[i]}{:trigger s[|s| - i - 1]} :: 0 <= i < |s| ==> s'[i] == s[|s| - i - 1]
  {
    if s == [] then [] else [s[|s|-1]] + Reverse(s[0 .. |s|-1])
  }
    
  function method {:opaque} Repeat<T>(v: T, length: nat): (s: seq<T>)
    ensures |s| == length
    ensures forall i: nat {:trigger s[i]} | i < |s| :: s[i] == v
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }
  
  /* unzips a sequence that contains ordered pairs into 2 seperate sequences */
  function method {:opaque} Unzip<A,B>(s: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(s).0| == |Unzip(s).1| == |s|
    ensures forall i {:trigger Unzip(s).0[i]} {:trigger Unzip(s).1[i]} 
        :: 0 <= i < |s| ==> (Unzip(s).0[i], Unzip(s).1[i]) == s[i]
  {
    if |s| == 0 then ([], [])
    else
      var (a, b):= Unzip(DropLast(s));
      (a + [Last(s).0], b + [Last(s).1])
  }

  /* takes two sequences, a and b, and combines then to form one sequence in which
  each position contains an ordered pair from a and b */
  function method {:opaque} Zip<A,B>(a: seq<A>, b: seq<B>): seq<(A, B)>
    requires |a| == |b|
    ensures |Zip(a, b)| == |a|
    ensures forall i {:trigger Zip(a, b)[i]}:: 0 <= i < |Zip(a, b)| ==> Zip(a, b)[i] == (a[i], b[i])
    ensures Unzip(Zip(a, b)).0 == a
    ensures Unzip(Zip(a, b)).1 == b
  {
    if |a| == 0 then []
    else Zip(DropLast(a), DropLast(b)) + [(Last(a), Last(b))]
  }

  /* if a sequence is unzipped and then zipped, it forms the original sequence */
  lemma LemmaZipOfUnzip<A,B>(s: seq<(A,B)>)
    ensures Zip(Unzip(s).0, Unzip(s).1) == s
  {
  }

  /**********************************************************
  *
  *  Extrema in Sequences
  *
  ***********************************************************/

  /* finds the maximum integer value in the sequence */
  function method {:opaque} Max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k {:trigger k in s} :: k in s ==> Max(s) >= k
    ensures Max(s) in s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then s[0] else Math.Max(s[0], Max(s[1..]))
  }

  /* the greater maximum value of two sequences, a and b, becomes the maximum of the total sequence when 
  a and b are concatenated */
  lemma LemmaMaxOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Max(a+b) >= Max(a)
    ensures Max(a+b) >= Max(b)
    ensures forall i {:trigger i in [Max(a + b)]} :: i in a + b ==> Max(a + b) >= i
  {
    reveal Max();
    if |a| == 1 {
    } else {
      assert a[1..] + b == (a + b)[1..];
      LemmaMaxOfConcat(a[1..], b);
    }
  }

  /* finds the minimum integer value in the sequence */
  function method {:opaque} Min(s: seq<int>): int
    requires 0 < |s|
    ensures forall k {:trigger k in s} :: k in s ==> Min(s) <= k
    ensures Min(s) in s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then s[0] else Math.Min(s[0], Min(s[1..]))
  }

  /* the smaller minimum value of two sequences, a and b, becomes the minimum of the total sequence when 
  a and b are concatenated */
  lemma LemmaMinOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Min(a+b) <= Min(a)
    ensures Min(a+b) <= Min(b)
    ensures forall i {:trigger i in a + b} :: i in a + b ==> Min(a + b) <= i
  {
    reveal Min();
    if |a| == 1 {
    } else {
      assert a[1..] + b == (a + b)[1..];
      LemmaMinOfConcat(a[1..], b);
    }
  }

  /* the maximum element in any subsequence will not be greater than the maximum element in 
  the full sequence */
  lemma LemmaSubseqMax(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Max(s[from..to]) <= Max(s)
  {
    var subseq := s[from..to];
    if Max(subseq) > Max(s) {
      var k :| 0 <= k < |subseq| && subseq[k] == Max(subseq);
      assert s[seq(|subseq|, i requires 0 <= i < |subseq| => i + from)[k]] in s;
      assert false;
    }
  }

  /* the minimum element in any subsequence will not be less than the minimum element in 
  the full sequence */
  lemma LemmaSubseqMin(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Min(s[from..to]) >= Min(s)
  {
    var subseq := s[from..to];
    if Min(subseq) < Min(s) {
      var k :| 0 <= k < |subseq| && subseq[k] == Min(subseq);
      assert s[seq(|subseq|, i requires 0 <= i < |subseq| => i + from)[k]] in s;
    }
  }

  /**********************************************************
  *
  *  Sequences of Sequences
  *
  ***********************************************************/

  /*concatenates a sequence of sequences into a single sequence. Works by adding 
  elements in order from first to last */
  function method Flatten<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then []
    else s[0] + Flatten(s[1..])
  }

  /* concatenating two sequences of sequences is equivalent to concatenating 
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
  lemma LemmaFlattenConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures Flatten(a + b) == Flatten(a) + Flatten(b)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc == {
        Flatten(a + b);
          { assert (a + b)[0] == a[0];  assert (a + b)[1..] == a[1..] + b; }
        a[0] + Flatten(a[1..] + b);
        a[0] + Flatten(a[1..]) + Flatten(b);
        Flatten(a) + Flatten(b);
      }
    }
  }

  /* concatenates the sequence of sequences into a single sequence. Works by concatenating 
  elements from last to first */
  function method FlattenReverse<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else FlattenReverse(DropLast(s)) + Last(s)
  }

  /* concatenating two reversed sequences of sequences is the same as reversing two 
  sequences of sequences and then concattenating the two resulting sequences together */
  lemma LemmaFlattenReverseConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
  ensures FlattenReverse(a + b) == FlattenReverse(a) + FlattenReverse(b)
  {
    if |b| == 0 {
      assert FlattenReverse(b) == [];
      assert a + b == a;
    } else {
      calc == {
        FlattenReverse(a + b);
          { assert Last(a + b) == Last(b);  assert DropLast(a + b) == a + DropLast(b); }
        FlattenReverse(a + DropLast(b)) + Last(b);
        FlattenReverse(a) + FlattenReverse(DropLast(b)) + Last(b);
        FlattenReverse(a) + FlattenReverse(b);
      }
    }
  }

  /* both methods of concatenating sequence (starting from front v. starting from back)
  result in the same sequence */
  lemma LemmaFlattenAndFlattenReverseAreEquivalent<T>(s: seq<seq<T>>)
    ensures Flatten(s) == FlattenReverse(s)
  {
    if |s| == 0 {
    } else {
      calc == {
        FlattenReverse(s);
        FlattenReverse(DropLast(s)) + Last(s);
          { LemmaFlattenAndFlattenReverseAreEquivalent(DropLast(s)); }
        Flatten(DropLast(s)) + Last(s);
        Flatten(DropLast(s)) + Flatten([Last(s)]);
          { LemmaFlattenConcat(DropLast(s), [Last(s)]); 
        assert s == DropLast(s) + [Last(s)]; }
        Flatten(s);
      }
    }
  }

  /* the concatenated sequence's length is greater than or equal to each individual
  inner sequence's length */
  lemma LemmaFlattenLengthGeSingleElementLength<T>(s: seq<seq<T>>, i: int)
    requires 0 <= i < |s|
    ensures |FlattenReverse(s)| >= |s[i]|
  {
    if i < |s| - 1 {
      LemmaFlattenLengthGeSingleElementLength(s[..|s|-1], i);
    }
  }

  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  lemma LemmaFlattenLengthLeMul<T>(s: seq<seq<T>>, j: int)
    requires forall i {:trigger s[i]} | 0 <= i < |s| :: |s[i]| <= j
    ensures |FlattenReverse(s)| <= |s| * j
  {
    if |s| == 0 {
    } else {
      LemmaFlattenLengthLeMul(s[..|s|-1], j);
    }
  }


  /**********************************************************
  *
  *  Higher-Order Sequence Functions
  *
  ***********************************************************/

  /* applies a transformation function on the sequence */
  function method {:opaque} Map<T,R>(f: (T ~> R), s: seq<T>): (result: seq<R>)
    requires forall i {:trigger s[i]} :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| == |s|
    ensures forall i {:trigger result[i]}:: 0 <= i < |s| ==> result[i] == f(s[i]);
    reads set i, o {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]):: o
  {
    if |s| == 0 then []
    else [f(s[0])] + Map(f, s[1..])
  }

/* applies a transformation function that returns a result on the sequence */
  function method {:opaque} MapWithResult<T, R, E>(f: (T ~> Result<R,E>), s: seq<T>): (result: Result<seq<R>, E>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures result.Success? ==>
      && |result.value| == |s|
      && (forall i :: 0 <= i < |s| ==> 
        && f(s[i]).Success?
        && result.value[i] == f(s[i]).value)
    reads set i, o | 0 <= i < |s| && o in f.reads(s[i]) :: o
  {
    if |s| == 0 then Success([])
    else
      var head :- f(s[0]);
      var tail :- MapWithResult(f, s[1..]);
      Success([head] + tail)
  }

  /* concatenating two sequences and then applying Map is the same as applying
  Map on each sequence  seperately and then concatenating the two resulting
  sequences */
  lemma {:opaque} LemmaMapDistributesOverConcat<T,R>(f: (T ~> R), a: seq<T>, b: seq<T>)
    requires forall i {:trigger a[i]}:: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j {:trigger b[j]}:: 0 <= j < |b| ==> f.requires(b[j])
    ensures Map(f, a + b) == Map(f, a) + Map(f, b)
  {
    reveal Map();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        Map(f, a + b);
          { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
        Map(f, [a[0]]) + Map(f, a[1..] + b);
        Map(f, [a[0]]) + Map(f, a[1..]) + Map(f, b);
          {assert [(a + b)[0]] + a[1..] + b == a + b;}
        Map(f, a) + Map(f, b);
      }
    }
  }

  /* uses a selection function to select elements from the sequence */
  function method {:opaque} Filter<T>(f: (T ~> bool), s: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| <= |s|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |s| == 0 then []
    else (if f(s[0]) then [s[0]] else []) + Filter(f, s[1..])
  }

  /* concatenating two sequences and then using "filter" is the same as using "filter" on each sequences
  seperately and then concatenating their resulting sequences */
  lemma {:opaque} LemmaFilterDistributesOverConcat<T>(f: (T ~> bool), a: seq<T>, b: seq<T>)
    requires forall i {:trigger a[i]}:: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j {:trigger b[j]}:: 0 <= j < |b| ==> f.requires(b[j])
    ensures Filter(f, a + b) == Filter(f, a) + Filter(f, b)
  {
    reveal Filter();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        Filter(f, a + b);
          { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
        Filter(f, [a[0]]) + Filter(f, a[1..] + b);
        Filter(f, [a[0]]) + Filter(f, a[1..]) + Filter(f, b);
          { assert [(a + b)[0]] + a[1..] + b == a + b; }
        Filter(f, a) + Filter(f, b);
      }
    }
  }
  
  function method {:opaque} FoldLeft<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else FoldLeft(f, f(init, s[0]), s[1..])
  }

  /* Concatenating two sequences, then folding left is the same as folding the first sequence and using the result as the initial value to fold the second
  sequence. */
  lemma {:opaque} LemmaFoldLeftDistributesOverConcat<A,T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldLeft(f, init, a + b) == FoldLeft(f, FoldLeft(f, init, a), b)
  {
    reveal FoldLeft();
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert |a| >= 1;
      assert ([a[0]] + a[1..] + b)[0] == a[0];
      calc {
        FoldLeft(f, FoldLeft(f, init, a), b);
        FoldLeft(f, FoldLeft(f, f(init, a[0]), a[1..]), b);
          { LemmaFoldLeftDistributesOverConcat(f, f(init, a[0]), a[1..], b); }
        FoldLeft(f, f(init, a[0]), a[1..] + b);
          { assert (a + b)[0] == a[0];
            assert (a + b)[1..] == a[1..] + b; }
        FoldLeft(f, init, a + b);
      }
    }
  }

  /* inv is an invariant under stp, which is a relational version of the
  function f passed to fold. */
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

  function method {:opaque} FoldRight<A,T>(f: (T, A) -> A, s: seq<T>, init: A): A
  {
    if |s| == 0 then init
    else f(s[0], FoldRight(f, s[1..], init))
  }

  /* Concatenating two sequences, then folding right is the same as folding the second sequence and using the result as the initial value to fold the first
  sequence. */
  lemma {:opaque} LemmaFoldRightDistributesOverConcat<A,T>(f: (T, A) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldRight(f, a + b, init) == FoldRight(f, a, FoldRight(f, b, init))
  {
    reveal FoldRight();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        FoldRight(f, a, FoldRight(f, b, init));
        f(a[0], FoldRight(f, a[1..], FoldRight(f, b, init)));
        f(a[0], FoldRight(f, a[1..] + b, init));
          { assert (a + b)[0] == a[0];
            assert (a + b)[1..] == a[1..] + b; }
        FoldRight(f, a + b, init);
      }
    }
  }

  /* inv is an invariant under stp, which is a relational version of the
  function f passed to fold. */
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
