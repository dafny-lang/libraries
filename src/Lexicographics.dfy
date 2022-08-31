// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Relations.dfy"

module Lexicographics {
    export 
    reveals LexicographicByteSeqBelow, LexicographicByteSeqBelowAux 
    provides Helpers, UInt, Relations

    import Helpers = Relations.Helpers
    import opened UInt = Helpers.UInt
    import opened Relations

  // reflexivelexicographical comparison of byte sequences
  predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>) 
  {
    LexicographicByteSeqBelowAux(x, y, 0)
  }

  predicate method LexicographicByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    || n == |x|
    || (n != |y| && x[n] < y[n])
    || (n != |y| && x[n] == y[n] && LexicographicByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutLexicographicByteSeqBelow()
    ensures TotalOrdering(LexicographicByteSeqBelow)
  {
    assert Reflexive(LexicographicByteSeqBelow) by {
      forall x, n | 0 <= n <= |x| {
        AboutLexicographicByteSeqBelowAux_Reflexive(x, n);
      }
    }
    assert AntiSymmetric(LexicographicByteSeqBelow) by {
      forall x, y, n: nat |
        n <= |x| && n <= |y| && x[..n] == y[..n] &&
        LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
      {
        AboutLexicographicByteSeqBelowAux_AntiSymmetric(x, y, n);
      }
    }
    assert Helpers.Transitive(LexicographicByteSeqBelow) by {
      forall x, y, z, n: nat |
        n <= |x| && n <= |y| && n <= |z| &&
        LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
      {
        AboutLexicographicByteSeqBelowAux_Transitive(x, y, z, n);
      }
    }
    assert Connected(LexicographicByteSeqBelow) by {
      forall x, y, n: nat | n <= |x| && n <= |y| {
        AboutLexicographicByteSeqBelowAux_Connected(x, y, n);
      }
    }
  }

  lemma AboutLexicographicByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures LexicographicByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
    ensures LexicographicByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma AboutLexicographicByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures LexicographicByteSeqBelowAux(x, y, n) || LexicographicByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }
}