// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*********************************************************************************************************************
Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
SPDX-License-Identifier: BSD-2-Clause
**********************************************************************************************************************/

include "../Options.dfy"
include "../Mathematics.dfy"

module Seq {

  import opened Options
  import Math = Mathematics

  /**********************************************************
  *
  Last in Sequences
  *
  ***********************************************************/
  
  /* finds the last element in the sequence */
  function method last<T>(s: seq<T>): T
    requires |s| > 0;
  {
    s[|s|-1]
  }

  /* returns the sequence slice up to but not including the last element */
  function method drop_last<T>(s: seq<T>): seq<T> 
    requires |s| > 0;
  {
    s[..|s|-1]
  }

  /* concatenating everything but the last element + the last element results in the original seq */
  lemma lemma_last<T>(s: seq<T>)
    requires |s| > 0;
    ensures  drop_last(s) + [last(s)] == s;
  {
  }

  /* the last element in an appended sequence will be the last element of the latter sequence */
  lemma lemma_append_last<T>(a: seq<T>, b: seq<T>)
    requires 0 < |a + b| && 0 < |b|
    ensures last(a + b) == last(b)
  {
  }

  /* explains associative property of sequences in addition */
  lemma lemma_concat_is_associative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == (a + b) + c;
  {
  }

  /**********************************************************
  *
  Contents and Placement in Sequence
  *
  ***********************************************************/
  
  predicate is_prefix<T>(a: seq<T>, b: seq<T>)
  {
    && |a| <= |b|
    && a == b[..|a|]    
  } 
  
  predicate is_suffix<T>(a: seq<T>, b: seq<T>) {
    && |a| <= |b|
    && a == b[|b|-|a|..]
  }

  /* a sequence that is sliced at the jth element concatenated with that same
  sequence sliced from the jth element is equal to the original, unsliced sequence */
  lemma lemma_split_at<T>(s: seq<T>, pos: nat)
    requires pos < |s|;
    ensures s[..pos] + s[pos..] == s;
  {
  }

  /* ensures that the element from a slice is included in the original sequence */
  lemma lemma_element_from_slice<T>(s: seq<T>, s':seq<T>, a:int, b:int, pos:nat)
    requires 0 <= a <= b <= |s|;
    requires s' == s[a..b];
    requires a <= pos < b;
    ensures  pos - a < |s'|;
    ensures  s'[pos-a] == s[pos];
  {
  }

  lemma lemma_slice_of_slice<T>(s: seq<T>, s1:int, e1:int, s2:int, e2:int)
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

  /* converts a sequence to a set */
  function method {:opaque} to_set<T>(s: seq<T>): set<T> 
  {
    set x: T | x in multiset(s)
  }

  /* proves that the cardinality of a subsequence is always less than or equal to that
  of the full sequence */
  lemma lemma_cardinality_of_set<T>(s: seq<T>)
    ensures |to_set(s)| <= |s| 
  {
    reveal_to_set();
    if |s| == 0 {
    } else {
      assert to_set(s) == to_set(drop_last(s)) + {last(s)};
      lemma_cardinality_of_set(drop_last(s));
    }
  }
  
  /* the cardinality of a subsequence of an empty sequence is also 0 */
  lemma lemma_cardinality_of_empty_set_is_0<T>(s: seq<T>)
    ensures |to_set(s)| == 0 <==> |s| == 0
  {
    reveal_to_set();
    if |s| != 0 {
      assert s[0] in to_set(s);
    }
  }

  /* is true if there are no duplicate values in the sequence */
  predicate {:opaque} has_no_duplicates<T>(s: seq<T>) 
  {
    (forall i, j {:trigger s[i], s[j]}:: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j])
  }

  /* if sequence a and b don't have duplicates, then the concatenated sequence of a + b
  will not contain duplicates either */
  lemma {:timeLimitMultiplier 3} lemma_no_duplicates_in_concat<T>(a: seq<T>, b: seq<T>)
    requires has_no_duplicates(a);
    requires has_no_duplicates(b);
    requires multiset(a) !! multiset(b);
    ensures has_no_duplicates(a+b);
  {
    reveal_has_no_duplicates();
    var c := a + b;
    if |c| > 1 {
      assert forall i, j {:trigger c[i], c[j]}:: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; 
    }
  }

  /* A sequence with no duplicates converts to a set of the same cardinality */
  lemma lemma_cardinality_of_set_no_duplicates<T>(s: seq<T>)
    requires has_no_duplicates(s)
    ensures |to_set(s)| == |s|
  {
    reveal_has_no_duplicates();
    reveal_to_set();
    if |s| == 0 {
    } else {
      lemma_cardinality_of_set_no_duplicates(drop_last(s));
      assert to_set(s) == to_set(drop_last(s)) + {last(s)};
    }
  }

  /* proves that there are no duplicate values in the multiset version of the sequence */
  lemma lemma_multiset_has_no_duplicates<T>(s: seq<T>)
    requires has_no_duplicates(s)
    ensures forall x {:trigger multiset(s)[x]} | x in multiset(s):: multiset(s)[x] == 1
  {
    if |s| == 0 {
    } else {
      assert s == drop_last(s) + [last(s)];
      assert last(s) !in drop_last(s) by {
        reveal_has_no_duplicates();
      }
      assert has_no_duplicates(drop_last(s)) by {
        reveal_has_no_duplicates();
      }
      lemma_multiset_has_no_duplicates(drop_last(s));
    }
  }

  /* finds the index of a certain element in the sequence if found*/
  function index_of<T>(s: seq<T>, v: T): Option<nat>
    requires v in s;
    ensures var i:= index_of(s, v);
    if i.Some? then i.value < |s| && s[i.value] == v else v !in s;
  {
    if i :| 0 <= i < |s| && s[i] == v then Some(i) else None
  }

  /* slices out a specific position's value from the sequence */
  function method {:opaque} remove<T>(s: seq<T>, pos: nat): seq<T>
    requires pos < |s|
    ensures |remove(s, pos)| == |s| - 1
    ensures forall i {:trigger remove(s, pos)[i], s[i]} | 0 <= i < pos :: remove(s, pos)[i] == s[i]
    ensures forall i {:trigger remove(s, pos)[i]} | pos <= i < |s| - 1 :: remove(s, pos)[i] == s[i+1]
  {
    s[..pos] + s[pos+1..] 
  }

  /* slices out a specific value from the sequence */
  function {:opaque} remove_value<T>(s: seq<T>, v: T): (s': seq<T>)
    ensures v !in s ==> s == s'
    ensures v in s ==> |multiset(s')| == |multiset(s)| - 1
    ensures v in s ==> multiset(s')[v] == multiset(s)[v] - 1
    ensures has_no_duplicates(s) ==> has_no_duplicates(s') && to_set(s') == to_set(s) - {v}
  {
    reveal_has_no_duplicates();
    reveal_to_set();
    if v !in s then s else
    var i :| 0 <= i < |s| && s[i] == v;
    assert s == s[..i] + [v] + s[i+1..];
    s[..i] + s[i+1..]
  }

  /* inserts a certain value into a specified index of the sequence */
  function method {:opaque} insert<T>(s: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |s|;
    ensures |insert(s, a, pos)| == |s| + 1;
    ensures forall i {:trigger insert(s, a, pos)[i], s[i]}:: 0 <= i < pos ==> insert(s, a, pos)[i] == s[i];
    ensures forall i {:trigger s[i]} :: pos <= i < |s| ==> insert(s, a, pos)[i+1] == s[i];
    ensures insert(s, a, pos)[pos] == a;
    ensures multiset(insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    assert s == s[..pos] + s[pos..];
    s[..pos] + [a] + s[pos..]
  }
    
  function method {:opaque} repeat<T>(v: T, length: nat): (s: seq<T>)
    ensures |s| == length
    ensures forall i: nat {:trigger s[i]} | i < |s| :: s[i] == v
  {
    if length == 0 then
      []
    else
      [v] + repeat(v, length - 1)
  }
  
  /* unzips a sequence that contains ordered pairs into 2 seperate sequences */
  function method {:opaque} unzip<A,B>(s: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |unzip(s).0| == |unzip(s).1| == |s|
    ensures forall i {:trigger unzip(s).0[i]} {:trigger unzip(s).1[i]} 
        :: 0 <= i < |s| ==> (unzip(s).0[i], unzip(s).1[i]) == s[i]
  {
    if |s| == 0 then ([], [])
    else
      var (a, b):= unzip(drop_last(s));
      (a + [last(s).0], b + [last(s).1])
  }

  /* takes two sequences, a and b, and combines then to form one sequence in which
  each position contains an ordered pair from a and b */
  function method {:opaque} zip<A,B>(a: seq<A>, b: seq<B>): seq<(A,B)>
    requires |a| == |b|
    ensures |zip(a, b)| == |a|
    ensures forall i {:trigger zip(a, b)[i]}:: 0 <= i < |zip(a, b)| ==> zip(a, b)[i] == (a[i], b[i])
    ensures unzip(zip(a, b)).0 == a;
    ensures unzip(zip(a, b)).1 == b;
  {
    if |a| == 0 then []
    else zip(drop_last(a), drop_last(b)) + [(last(a), last(b))]
  }

  /* if a sequence is unzipped and then zipped, it forms the original sequence */
  lemma lemma_zip_of_unzip<A,B>(s: seq<(A,B)>)
    ensures zip(unzip(s).0, unzip(s).1) == s
  {
  }

  /**********************************************************
  *
  Extrema in Sequences
  *
  ***********************************************************/

  /* finds the maximum integer value in the sequence */
  function method {:opaque} max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k {:trigger k in s} :: k in s ==> max(s) >= k
    ensures max(s) in s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then s[0] else Math.max(s[0], max(s[1..]))
  }

  /* the greater maximum value of two sequences, a and b, becomes the maximum of the total sequence when 
  a and b are concatenated */
  lemma lemma_max_of_concat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures max(a+b) >= max(a)
    ensures max(a+b) >= max(b)
    ensures forall i {:trigger i in [max(a + b)]} :: i in a + b ==> max(a + b) >= i
  {
    reveal_max();
    if |a| == 1 {
    } else {
      assert a[1..] + b == (a + b)[1..];
      lemma_max_of_concat(a[1..], b);
    }
  }

  /* finds the minimum integer value in the sequence */
  function method {:opaque} min(s: seq<int>): int
    requires 0 < |s|
    ensures forall k {:trigger k in s} :: k in s ==> min(s) <= k
    ensures min(s) in s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then s[0] else Math.min(s[0], min(s[1..]))
  }

  /* the smaller minimum value of two sequences, a and b, becomes the minimum of the total sequence when 
  a and b are concatenated */
   lemma lemma_min_of_concat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures min(a+b) <= min(a)
    ensures min(a+b) <= min(b)
    ensures forall i {:trigger i in a + b} :: i in a + b ==> min(a + b) <= i
  {
    reveal_min();
    if |a| == 1 {
    } else {
      assert a[1..] + b == (a + b)[1..];
      lemma_min_of_concat(a[1..], b);
    }
  }

  /* the maximum element in any subsequence will not be greater than the maximum element in 
  the full sequence */
  lemma lemma_subseq_max(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures max(s[from..to]) <= max(s)
  {
    var subseq := s[from..to];
    if max(subseq) > max(s) {
      var k :| 0 <= k < |subseq| && subseq[k] == max(subseq);
      assert s[seq(|subseq|, i requires 0 <= i < |subseq| => i + from)[k]] in s;
      assert false;
    }
  }

  /* the minimum element in any subsequence will not be less than the minimum element in 
  the full sequence */
  lemma lemma_subseq_min(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures min(s[from..to]) >= min(s)
  {
    var subseq := s[from..to];
    if min(subseq) < min (s) {
      var k :| 0 <= k < |subseq| && subseq[k] == min(subseq);
      assert s[seq(|subseq|, i requires 0 <= i < |subseq| => i + from)[k]] in s;
    }
  }

  /**********************************************************
  *
  Sequences of Sequences
  *
  ***********************************************************/

  /*concatenates a sequence of sequences into a single sequence. Works by adding 
  elements in order from first to last */
  function method flatten<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else s[0] + flatten(s[1..])
  }

  /* concatenating two sequences of sequences is equivalent to concatenating 
  each sequence of sequences seperately, and then concatenating the two resulting 
  sequences together */
  lemma lemma_flatten_concat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures flatten(a + b) == flatten(a) + flatten(b)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc == {
        flatten(a + b);
          { assert (a + b)[0] == a[0];  assert (a + b)[1..] == a[1..] + b; }
        a[0] + flatten(a[1..] + b);
        a[0] + flatten(a[1..]) + flatten(b);
        flatten(a) + flatten(b);
      }
    }
  }

  /* concatenates the sequence of sequences into a single sequence. Works by concatenating 
  elements from last to first */
  function method flatten_reverse<T>(s: seq<seq<T>>): seq<T>
  decreases |s|
  {
    if |s| == 0 then []
    else flatten_reverse(drop_last(s)) + last(s)
  }

  /* concatenating two reversed sequences of sequences is the same as reversing two 
  sequences of sequences and then concattenating the two resulting sequences together */
  lemma lemma_flatten_reverse_concat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
  ensures flatten_reverse(a + b) == flatten_reverse(a) + flatten_reverse(b)
  {
    if |b| == 0 {
      assert flatten_reverse(b) == [];
      assert a + b == a;
    } else {
      calc == {
        flatten_reverse(a + b);
          { assert last(a + b) == last(b);  assert drop_last(a + b) == a + drop_last(b); }
        flatten_reverse(a + drop_last(b)) + last(b);
        flatten_reverse(a) + flatten_reverse(drop_last(b)) + last(b);
        flatten_reverse(a) + flatten_reverse(b);
      }
    }
  }

  /* both methods of concatenating sequence (starting from front v. starting from back)
  result in the same sequence */
  lemma lemma_flatten_and_flatten_reverse_are_equivalent<T>(s: seq<seq<T>>)
    ensures flatten(s) == flatten_reverse(s)
  {
    if |s| == 0 {
    } else {
      calc == {
        flatten_reverse(s);
        flatten_reverse(drop_last(s)) + last(s);
          { lemma_flatten_and_flatten_reverse_are_equivalent(drop_last(s)); }
        flatten(drop_last(s)) + last(s);
        flatten(drop_last(s)) + flatten([last(s)]);
          { lemma_flatten_concat(drop_last(s), [last(s)]); 
        assert s == drop_last(s) + [last(s)]; }
        flatten(s);
      }
    }
  }

  /* the concatenated sequence's length is greater than or equal to each individual
  inner sequence's length */
  lemma lemma_flatten_length_ge_single_element_length<T>(s: seq<seq<T>>, i: int)
    requires 0 <= i < |s|
    ensures |flatten_reverse(s)| >= |s[i]|
  {
    if i < |s| - 1 {
      lemma_flatten_length_ge_single_element_length(s[..|s|-1], i);
    }
  }

  /* the length of concatenating sequence in a sequence together will be no longer 
  than the length of the original sequence of sequences multiplied by the length of 
  the longest sequence */
  lemma lemma_flatten_length_le_mul<T>(s: seq<seq<T>>, j: int)
    requires forall i {:trigger s[i]} | 0 <= i < |s| :: |s[i]| <= j
    ensures |flatten_reverse(s)| <= |s| * j
  {
    if |s| == 0 {
    } else {
      lemma_flatten_length_le_mul(s[..|s|-1], j);
    }
  }


  /**********************************************************
  *
  Higher Order Sequence Functions
  *
  ***********************************************************/

  /* applies a transformation function on the sequence; this acts as "map" in other languages */
  function method {:opaque} apply<T,R>(f: (T ~> R), s: seq<T>): (result: seq<R>)
    requires forall i {:trigger s[i]} :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| == |s|
    ensures forall i {:trigger result[i]}:: 0 <= i < |s| ==> result[i] == f(s[i]);
    reads set i, o {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]):: o
  {
    if |s| == 0 then []
    else  [f(s[0])] + apply(f, s[1..])
  }

  /* concatenating two sequences and then using "apply" is the same as using "apply" on each sequence 
  seperately and then concatenating the two resulting sequences */
  lemma {:opaque} lemma_apply_concat<T,R>(f: (T ~> R), a: seq<T>, b: seq<T>)
    requires forall i {:trigger a[i]}:: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j {:trigger b[j]}:: 0 <= j < |b| ==> f.requires(b[j])
    ensures apply(f, a + b) == apply(f, a) + apply(f, b)
  {
    reveal_apply();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        apply(f, a + b);
          { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
        apply(f, [a[0]]) + apply(f, a[1..] + b);
        apply(f, [a[0]]) + apply(f, a[1..]) + apply(f, b);
          {assert [(a + b)[0]] + a[1..] + b == a + b;}
        apply(f, a) + apply(f, b);
      }
    }
  }

  /* uses a selection function to select elements from the sequence */
  function method {:opaque} filter<T>(f: (T ~> bool), s: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |s| ==> f.requires(s[i])
    ensures |result| <= |s|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |s| == 0 then []
    else ((if f(s[0]) then [s[0]] else []) + filter(f, s[1..]))
  }

  /* concatenating two sequences and then using "filter" is the same as using "filter" on each sequences
  seperately and then concatenating their resulting sequences */
  lemma {:opaque} lemma_filter_concat<T>(f: (T ~> bool), a: seq<T>, b: seq<T>)
    requires forall i {:trigger a[i]}:: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j {:trigger b[j]}:: 0 <= j < |b| ==> f.requires(b[j])
    ensures filter(f, a + b) == filter(f, a) + filter(f, b)
  {
    reveal_filter();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        filter(f, a + b);
          { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
        filter(f, [a[0]]) + filter(f, a[1..] + b);
        filter(f, [a[0]]) + filter(f, a[1..]) + filter(f, b);
          { assert [(a + b)[0]] + a[1..] + b == a + b; }
        filter(f, a) + filter(f, b);
      }
    }
  }
  
  function method {:opaque} fold_left<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else fold_left(f, f(init, s[0]), s[1..])
  }

  lemma {:opaque} lemma_fold_left_concat<A,T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures fold_left(f, init, a + b) == fold_left(f, fold_left(f, init, a), b)
  {
    reveal_fold_left();
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert |a| >= 1;
      assert ([a[0]] + a[1..] + b)[0] == a[0];
      calc {
        fold_left(f, fold_left(f, init, a), b);
        fold_left(f, fold_left(f, f(init, a[0]), a[1..]), b);
          { lemma_fold_left_concat(f, f(init, a[0]), a[1..], b); }
        fold_left(f, f(init, a[0]), a[1..] + b);
          { assert (a + b)[0] == a[0];
            assert (a + b)[1..] == a[1..] + b; }
        fold_left(f, init, a + b);
      }
    }
  }

  function method {:opaque} fold_right<A,T>(f: (T, A) -> A, s: seq<T>, init: A): A
  {
    if |s| == 0 then init
    else f(s[0], fold_right(f, s[1..], init))
  }

  lemma {:opaque} lemma_fold_right_concat<A,T>(f: (T, A) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures fold_right(f, a + b, init) == fold_right(f, a, fold_right(f, b, init))
  {
    reveal_fold_right();
    if |a| == 0 {
      assert a + b == b;
    } else {
      calc {
        fold_right(f, a, fold_right(f, b, init));
        f(a[0], fold_right(f, a[1..], fold_right(f, b, init)));
        f(a[0], fold_right(f, a[1..] + b, init));
          { assert (a + b)[0] == a[0];
            assert (a + b)[1..] == a[1..] + b; }
        fold_right(f, a + b, init);
      }
    }
  }

}
