// RUN: %dafny /compile:0 "%s"

include "../../StandardLibrary.dfy"
include "../../UInt.dfy"



module BinarySearch{
  export
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering
    reveals LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow
    provides StandardLibrary, UInt

  import StandardLibrary
  import opened UInt = StandardLibrary.UInt

  

predicate Reflexive<T(!new)>(R: (T, T) -> bool) {
    forall x :: R(x, x)
  }

predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) && R(y, x) ==> x == y
  }

predicate Connected<T(!new)>(R: (T, T) -> bool) {
    forall x, y :: R(x, y) || R(y, x)
  }

predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) {
    && Reflexive(R)
    && AntiSymmetric(R)
    && StandardLibrary.Transitive(R)
    && Connected(R)
  }

predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>) {
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
    assert StandardLibrary.Transitive(LexicographicByteSeqBelow) by {
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

datatype Option<T> = None | Some(T)

method BinarySearch<T>(a: array<T>, key: T,compare: (T, T) -> bool) returns (r:Option<nat>)
  requires forall i,j :: 0 <= i < j < a.Length ==> compare(a[i], a[j]) || a[i] == a[j]
  requires StandardLibrary.Trichotomous(compare)
  ensures 0 <= r ==> r <= a.Length && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi : Option<nat> := Some(0), Some(a.Length);
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if compare(key , a[mid]) {
      hi := mid;
    } else if compare(a[mid] , key) {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return None;
}
}