// RUN: %verify "%s"

/*******************************************************************************
 * Original: Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University,
 * ETH Zurich, and University of Washington
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Modifications and Extensions: Copyright by the contributors to the Dafny Project
 * SPDX-License-Identifier: MIT
 ******************************************************************************/

include "../../Wrappers.dfy"
include "../../Functions.dfy"
include "../Sets/Sets.dfy"

module {:options "-functionSyntax:4"} Maps {
  import opened Wrappers
  import Functions
  import Sets

  function Get<X, Y>(m: map<X, Y>, x: X): Option<Y>
  {
    if x in m then Some(m[x]) else None
  }

  function {:opaque} ToImap<X, Y>(m: map<X, Y>): (m': imap<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m
  {
    imap x | x in m :: m[x]
  }

  /* Remove all key-value pairs corresponding to the set of keys provided. */
  function {:opaque} RemoveKeys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    m - xs
  }

  /* Remove a key-value pair. Returns unmodified map if key is not found. */
  function {:opaque} Remove<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }

  /* Keep all key-value pairs corresponding to the set of keys provided. */
  function {:opaque} Restrict<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, m.Keys - xs)
  {
    map x | x in xs && x in m :: m[x]
  }

  /* True iff x maps to the same value or does not exist in m and m'. */
  ghost predicate EqualOnKey<X, Y>(m: map<X, Y>, m': map<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  /* True iff m is a subset of m'. */
  ghost predicate IsSubset<X, Y>(m: map<X, Y>, m': map<X, Y>)
  {
    && m.Keys <= m'.Keys
    && forall x <- m :: m[x] == m'[x]
  }

  /* Union of two maps. Does not require disjoint domains; on the intersection,
  values from the second map are chosen. */
  function {:opaque} Union<X, Y>(m: map<X, Y>, m': map<X, Y>): (r: map<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x {:trigger r[x]} :: x in m' ==> r[x] == m'[x]
    ensures forall x {:trigger r[x]} :: x in m && x !in m' ==> r[x] == m[x]
  {
    m + m'
  }

  /* The size of the disjoint union is equal to the sum of individual map
  sizes. */
  lemma LemmaDisjointUnionSize<X, Y>(m: map<X, Y>, m': map<X, Y>)
    requires m.Keys !! m'.Keys
    ensures |Union(m, m')| == |m| + |m'|
  {
    var u := Union(m, m');
    assert |u.Keys| == |m.Keys| + |m'.Keys|;
  }

  /* True iff a map is injective. */
  ghost predicate {:opaque} Injective<X, Y>(m: map<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x != x' && x in m && x' in m ==> m[x] != m[x']
  }

  lemma LemmaSubsetIsInjective<X, Y>(small: map<X, Y>, big: map<X, Y>)
    requires IsSubset(small, big)
    requires Injective(big)
    ensures Injective(small)
  {
    reveal Injective();
  }

  lemma LemmaInjectiveImpliesUniqueValues<X(!new), Y>(m: map<X, Y>)
    requires Injective(m)
    ensures |m.Keys| == |m.Values|
  {
    if |m| > 0 {
      reveal Injective();

      var x: X :| x in m;
      var y := m[x];
      var m' := Remove(m, x);
      assert IsSubset(m', m);

      assert m'.Values == m.Values - {y};
      LemmaSubsetIsInjective(m', m);
      LemmaInjectiveImpliesUniqueValues(m');
    }
  }

  /* Swaps map keys and values. Values are not required to be unique; no
  promises on which key is chosen on the intersection. */
  ghost function {:opaque} Invert<X, Y>(m: map<X, Y>): map<Y, X>
  {
    map y | y in m.Values :: var x :| x in m.Keys && m[x] == y; x
  }

  /* Inverted maps are injective. */
  lemma LemmaInvertIsInjective<X, Y>(m: map<X, Y>)
    ensures Injective(Invert(m))
  {
    reveal Injective();
    reveal Invert();
  }

  /* True iff a map contains all valid keys. */
  ghost predicate {:opaque} Total<X(!new), Y>(m: map<X, Y>)
  {
    forall i {:trigger m[i]}{:trigger i in m} :: i in m
  }

  /* True iff a map is monotonic. */
  ghost predicate {:opaque} Monotonic(m: map<int, int>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  /* True iff a map is monotonic. Only considers keys greater than or
  equal to start. */
  ghost predicate {:opaque} MonotonicFrom(m: map<int, int>, start: int)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

  /* Maps an injective function over the keys of a map, retaining the values. */
  function {:opaque} MapKeys<X(!new), Y, X'>(f: X --> X', m: map<X, Y>): (m': map<X', Y>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Functions.Injective(f)
    ensures |m'| == |m|
    ensures m'.Values == m.Values
    ensures forall x | x in m :: f(x) in m' && (m'[f(x)] == m[x])
  {
    var m' := map k <- m :: f(k) := m[k];
    Sets.LemmaMapSize(m.Keys, m'.Keys, f);
    m'
  }

  /* Maps a function over the values of a map, retaining the keys. */
  function {:opaque} MapValues<X, Y(!new), Y'>(f: Y --> Y', m: map<X, Y>): (m': map<X, Y'>)
    reads f.reads
    requires forall y {:trigger f.requires(y)} :: f.requires(y)
    ensures |m'| == |m|
    ensures m'.Keys == m.Keys
    ensures forall x | x in m :: m'[x] == f(m[x])
  {
    var m' := map x <- m :: x := f(m[x]);
    assert |m'| == |m| by {
      assert m'.Keys == m.Keys;
      assert |m'.Keys| == |m.Keys|;
    }
    m'
  }
}
