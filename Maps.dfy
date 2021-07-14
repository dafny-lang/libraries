// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
SPDX-License-Identifier: BSD-2-Clause */

include "../Options.dfy"

module Maps {
  import opened Options

  function method get<X, Y>(m: map<X, Y>, x: X): Option<Y>
  {
	  if x in m then Some(m[x]) else None
	}

  function method {:opaque} to_imap<X, Y>(m: map<X, Y>): (m': imap<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m
  {
	  imap x | x in m :: m[x]
	}

  /* Remove all key-value pairs corresponding to the set of keys provided. */
  function method {:opaque} remove_keys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    map x | x in m && x !in xs :: m[x]
  }

  /* Remove a key-value pair. Returns unmodified map if key is not found. */
  function method {:opaque} remove<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == remove_keys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }

  /* Keep all key-value pairs corresponding to the set of keys provided. */
  function method {:opaque} restrict<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures m' == remove_keys(m, m.Keys - xs)
  {
    map x | x in xs && x in m :: m[x]
  }

  /* True iff two maps contain the same key-value pairs for intersecting
  keys. */
  predicate equal_on_key<X, Y>(m: map<X, Y>, m': map<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  /* True iff m is a subset of m'. */
  predicate is_subset<X, Y>(m: map<X, Y>, m': map<X, Y>)
  {
    && m.Keys <= m'.Keys
    && forall x {:trigger equal_on_key(m, m', x)}{:trigger x in m} :: x in m ==> equal_on_key(m, m', x)
  }

  /* Union of two maps. Does not require disjoint domains; on the intersection,
  values from the first map are chosen. */
  function method {:opaque} union<X, Y>(m: map<X, Y>, m': map<X, Y>): (r: map<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x {:trigger r[x]} :: x in m ==> r[x] == m[x]
    ensures forall x {:trigger r[x]} :: x in m' && x !in m ==> r[x] == m'[x]
  {
    map x | x in m.Keys + m'.Keys :: if x in m then m[x] else m'[x]
  }

  /* The size of the disjoint union is equal to the sum of individual map
  sizes. */
  lemma lemma_disjoint_union_size<X, Y>(m: map<X, Y>, m': map<X, Y>)
    requires m.Keys !! m'.Keys
    ensures |union(m, m')| == |m| + |m'|
  {
    var u := union(m, m');
    assert |u.Keys| == |m.Keys| + |m'.Keys|;
  }

  /* True iff a map is injective. */
  predicate {:opaque} injective<X, Y>(m: map<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x != x' && x in m && x' in m ==> m[x] != m[x']
  }

  /* Swaps map keys and values. Values are not required to be unique; no
  promises on which key is chosen on the intersection. */
  function {:opaque} invert<X, Y>(m: map<X, Y>): map<Y, X>
  {
    map y | y in m.Values :: var x :| x in m.Keys && m[x] == y; x
  }

  /* Inverted maps are injective. */
  lemma lemma_invert_is_injective<X, Y>(m: map<X, Y>)
    ensures injective(invert(m))
  {
    reveal_injective();
    reveal_invert();
  }

  /* True iff a map contains all valid keys. */
  predicate {:opaque} total<X(!new), Y>(m: map<X, Y>)
  {
    forall i {:trigger m[i]}{:trigger i in m} :: i in m
  }

  /* True iff a map is monotonic. */
  predicate {:opaque} monotonic(m: map<int, int>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  /* True iff a map is monotonic. Only considers keys greater than or
  equal to start. */
  predicate {:opaque} monotonic_from(m: map<int, int>, start: int)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

}
