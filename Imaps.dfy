// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
SPDX-License-Identifier: BSD-2-Clause */

include "../Options.dfy"

module Imaps {
  import opened Options

  function method get<X, Y>(m: imap<X, Y>, x: X): Option<Y>
  {
	  if x in m then Some(m[x]) else None
	}

  /* Remove all key-value pairs corresponding to the iset of keys provided. */
  function {:opaque} remove_keys<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    imap x | x in m && x !in xs :: m[x]
  }

  /* Remove a key-value pair. Returns unmodified imap if key is not found. */
  function {:opaque} remove<X, Y>(m: imap<X, Y>, x: X): (m': imap<X, Y>)
    ensures m' == remove_keys(m, iset{x})
    ensures forall x' {:trigger m'[x']} :: x' in m' ==> m'[x'] == m[x']
  {
    imap i | i in m && i != x :: m[i]
  }

  /* Keep all key-value pairs corresponding to the iset of keys provided. */
  function {:opaque} restrict<X, Y>(m: imap<X, Y>, xs: iset<X>): (m': imap<X, Y>)
    ensures m' == remove_keys(m, m.Keys - xs)
  {
    imap x | x in xs && x in m :: m[x]
  }

  /* True iff two imaps contain the same key-value pairs for intersecting
  keys. */
  predicate equal_on_key<X, Y>(m: imap<X, Y>, m': imap<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  /* True iff m is a subset of m'. */
  predicate is_subset<X, Y>(m: imap<X, Y>, m': imap<X, Y>)
  {
    && m.Keys <= m'.Keys
    && forall x {:trigger equal_on_key(m, m', x)}{:trigger x in m} :: x in m ==> equal_on_key(m, m', x)
  }

  /* Union of two imaps. Does not require disjoint domains; on the intersection,
  values from the first imap are chosen. */
  function {:opaque} union<X, Y>(m: imap<X, Y>, m': imap<X, Y>): (r: imap<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x {:trigger r[x]} :: x in m ==> r[x] == m[x]
    ensures forall x {:trigger r[x]} :: x in m' && x !in m ==> r[x] == m'[x]
  {
    imap x | x in m.Keys + m'.Keys :: if x in m then m[x] else m'[x]
  }

  /* True iff an imap is injective. */
  predicate {:opaque} injective<X, Y>(m: imap<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x != x' && x in m && x' in m ==> m[x] != m[x']
  }
  
  /* Swaps imap keys and values. Values are not required to be unique; no
  promises on which key is chosen on the intersection. */
  function {:opaque} invert<X, Y>(m: imap<X, Y>): imap<Y, X>
  {
    imap y | y in m.Values :: var x :| x in m.Keys && m[x] == y; x
  }

  /* Inverted maps are injective. */
  lemma lemma_invert_is_injective<X, Y>(m: imap<X, Y>)
    ensures injective(invert(m))
  {
    reveal_injective();
    reveal_invert();
  }

  /* True iff an imap contains all valid keys. */
  predicate {:opaque} total<X(!new), Y>(m: imap<X, Y>)
  {
    forall i {:trigger m[i]}{:trigger i in m} :: i in m
  }

  /* True iff an imap is monotonic. */
  predicate {:opaque} monotonic(m: imap<int, int>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  /* True iff an imap is monotonic. Only considers keys greater than or
  equal to start. */
  predicate {:opaque} monotonic_from(m: imap<int, int>, start: int)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

}
