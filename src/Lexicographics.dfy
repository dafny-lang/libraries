// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Relations/Relations.dfy"
include "UInt.dfy"

module Lexicographics {
    export 
        reveals ByteSeqBelow, ByteSeqBelowAux
        provides Relations, UInt

    import opened Relations
    import opened UInt


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
}