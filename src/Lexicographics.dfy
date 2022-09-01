// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Relations.dfy"
include "UInt.dfy"

module Lexicographics {
    export 
        reveals ByteSeqBelow, ByteSeqBelowAux
        provides  LessOrEqual, LessOrEqualAux
        provides Relations, UInt

    import opened Relations
    import opened UInt = Helpers.UInt

  // reflexivelexicographical comparison of byte sequences
  predicate method ByteSeqBelow(x: seq<uint8>, y: seq<uint8>) 
  {
    ByteSeqBelowAux(x, y, 0)
  }

  predicate method ByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    || n == |x|
    || (n != |y| && x[n] < y[n])
    || (n != |y| && x[n] == y[n] && ByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutByteSeqBelow()
    ensures TotalOrdering(ByteSeqBelow)
  {
    assert Reflexive(ByteSeqBelow) by {
      forall x, n | 0 <= n <= |x| {
        AboutByteSeqBelowAux_Reflexive(x, n);
      }
    }
    assert AntiSymmetric(ByteSeqBelow) by {
      forall x, y, n: nat |
        n <= |x| && n <= |y| && x[..n] == y[..n] &&
        ByteSeqBelowAux(x, y, n) && ByteSeqBelowAux(y, x, n)
      {
        AboutByteSeqBelowAux_AntiSymmetric(x, y, n);
      }
    }
    assert Relations.Transitive(ByteSeqBelow) by {
      forall x, y, z, n: nat |
        n <= |x| && n <= |y| && n <= |z| &&
        ByteSeqBelowAux(x, y, n) && ByteSeqBelowAux(y, z, n)
      {
        AboutByteSeqBelowAux_Transitive(x, y, z, n);
      }
    }
    assert Connected(ByteSeqBelow) by {
      forall x, y, n: nat | n <= |x| && n <= |y| {
        AboutByteSeqBelowAux_Connected(x, y, n);
      }
    }
  }

  lemma AboutByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures ByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma AboutByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires ByteSeqBelowAux(x, y, n) && ByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma AboutByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires ByteSeqBelowAux(x, y, n) && ByteSeqBelowAux(y, z, n)
    ensures ByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma AboutByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures ByteSeqBelowAux(x, y, n) || ByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }

  /*
   * Lexicographic comparison of sequences.
   *
   * Given two sequences `a` and `b` and a strict (that is, irreflexive)
   * ordering `less` on the elements of these sequences, determine whether or not
   * `a` is lexicographically "less than or equal to" `b`.
   *
   * `a` is lexicographically "less than or equal to" `b` holds iff
   *   there exists a `k` such that
   *   - the first `k` elements of `a` and `b` are the same
   *   - either:
   *      -- `a` has length `k` (that is, `a` is a prefix of `b`)
   *      -- `a[k]` is strictly less (using `less`) than `b[k]`
   */

  predicate method LessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool) {
    exists k :: 0 <= k <= |a| && LessOrEqualAux(a, b, less, k)
  }

  predicate method LessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
  {
    lengthOfCommonPrefix <= |b|
    && (forall i :: 0 <= i < lengthOfCommonPrefix ==> a[i] == b[i])
    && (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

}