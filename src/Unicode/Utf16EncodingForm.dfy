// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Collections/Sequences/Seq.dfy"
include "../Functions.dfy"

include "Unicode.dfy"
include "UnicodeEncodingForm.dfy"

// Definition of the UTF-16 Unicode Encoding Form, as specified in Section 3.9 D91.
module Utf16EncodingForm refines UnicodeEncodingForm {
  type CodeUnit = bv16

  //
  // Definitions of well-formedness.
  //

  function method IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
  {
    if |s| == 1 then IsWellFormedSingleCodeUnitSequence(s)
    else if |s| == 2 then (
      var b := IsWellFormedDoubleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    )
    else false
  }

  function method IsWellFormedSingleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 1
  {
    var firstWord := s[0];
    || 0x0 <= firstWord <= 0xD7FF
    || 0xE000 <= firstWord <= 0xFFFF
  }

  function method IsWellFormedDoubleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 2
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1])
  {
    var firstWord := s[0];
    var secondWord := s[1];
    && 0xD800 <= firstWord <= 0xDBFF
    && 0xDC00 <= secondWord <= 0xDFFF
  }

  function method SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==>
      && maybePrefix.Some?
    ensures maybePrefix.Some? ==>
      && var prefix := maybePrefix.Extract();
      && 0 < |prefix| <= |s|
      && prefix == s[..|prefix|]
      && IsMinimalWellFormedCodeUnitSubsequence(prefix)
  {
    if |s| >= 1 && IsWellFormedSingleCodeUnitSequence(s[..1]) then Some(s[..1])
    else if |s| >= 2 && IsWellFormedDoubleCodeUnitSequence(s[..2]) then Some(s[..2])
    else None
  }

  //
  // Encoding and decoding.
  // See Table 3-5. UTF-16 Bit Distribution.
  //

  function method EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
  {
    if 0x0 <= v <= 0xD7FF || 0xE000 <= v <= 0xFFFF then EncodeScalarValueSingleWord(v)
    else EncodeScalarValueDoubleWord(v)
  }

  function method EncodeScalarValueSingleWord(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires
      || 0x0 <= v <= 0xD7FF
      || 0xE000 <= v <= 0xFFFF
    ensures |m| == 1
    ensures IsWellFormedSingleCodeUnitSequence(m)
  {
    var firstWord := v as CodeUnit;
    [firstWord]
  }

  function method EncodeScalarValueDoubleWord(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 0x10000 <= v <= 0x10FFFF
    ensures |m| == 2
    ensures IsWellFormedDoubleCodeUnitSequence(m)
  {
    // v = 000u uuuu / xxxx xxxx / xxxx xxxx
    //                 1111 1122   2222 2222
    var x2 := (v & 0x3FF) as bv10;
    var x1 := ((v & 0xFC00) >> 10) as bv6;
    var u := ((v & 0x1F0000) >> 16) as bv5;
    var w := (u - 1) as bv4;
    // encoded = 1101 10ww / wwxx xxxx / 1101 11xx / xxxx xxxx
    //                         11 1111          22   2222 2222
    var firstWord := 0xD800 | ((w as CodeUnit) << 6) | x1 as CodeUnit;
    var secondWord := 0xDC00 | x2 as CodeUnit;
    [firstWord, secondWord]
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
  {
    if |m| == 1 then DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
    else assert |m| == 2; DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 1
    ensures
      || 0x0 <= v <= 0xD7FF
      || 0xE000 <= v <= 0xFFFF
    ensures EncodeScalarValueSingleWord(v) == m
  {
    var firstWord := m[0];
    var x := firstWord as bv16;
    assert EncodeScalarValueSingleWord(x as Unicode.ScalarValue) == m;
    x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 2
    ensures 0x10000 <= v <= 0x10FFFF
    ensures EncodeScalarValueDoubleWord(v) == m
  {
    var firstWord := m[0];
    var secondWord := m[1];
    var x2 := (secondWord & 0x3FF) as bv24;
    var x1 := (firstWord & 0x3F) as bv24;
    var w := ((firstWord & 0x3C0) >> 6) as bv24;
    var u := (w + 1) as bv24;
    var v := (u << 16) | (x1 << 10) | x2 as Unicode.ScalarValue;
    assert {:split_here} true;
    assert EncodeScalarValueDoubleWord(v) == m;
    v
  }

  //
  // Tests
  //

  const TEST_SCALAR_VALUES: seq<(Unicode.ScalarValue, WellFormedCodeUnitSeq)> := [
    // One code unit: dollar sign
    (0x0024, [0x0024]),
    // Two code units: money bag emoji
    (0x1F4B0, [0xD83D, 0xDCB0])
  ]

  lemma TestEncodeScalarValue()
    ensures forall pair | pair in TEST_SCALAR_VALUES
      :: EncodeScalarValue(pair.0) == pair.1
  {}
}
