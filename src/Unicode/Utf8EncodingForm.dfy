// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Collections/Sequences/Seq.dfy"
include "../Functions.dfy"

include "Unicode.dfy"
include "UnicodeEncodingForm.dfy"

/**
 * The Unicode encoding form that assigns each Unicode scalar value to an unsigned byte sequence of one to four bytes
 * in length, as specified in Table 3-6 and Table 3-7.
 */
module Utf8EncodingForm refines UnicodeEncodingForm {
  type CodeUnit = bv8

  //
  // Definitions of well-formedness.
  //

  function method IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
  {
    if |s| == 1 then (
      var b := IsWellFormedSingleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    )
    else if |s| == 2 then (
      var b := IsWellFormedDoubleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    )
    else if |s| == 3 then (
      var b := IsWellFormedTripleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    )
    else if |s| == 4 then (
      var b := IsWellFormedQuadrupleCodeUnitSequence(s);
      assert b ==> forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    )
    else false
  }

  function method IsWellFormedSingleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 1
  {
    var firstByte := s[0];
    && 0x00 <= firstByte <= 0x7F
  }

  function method IsWellFormedDoubleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 2
    ensures b ==>
      && !IsWellFormedSingleCodeUnitSequence(s[..1])
  {
    var firstByte := s[0];
    var secondByte := s[1];
    && 0xC2 <= firstByte <= 0xDF
    && 0x80 <= secondByte <= 0xBF
  }

  function method IsWellFormedTripleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 3
    ensures b ==>
      && !IsWellFormedSingleCodeUnitSequence(s[..1])
      && !IsWellFormedDoubleCodeUnitSequence(s[..2])
  {
    var firstByte := s[0];
    var secondByte := s[1];
    var thirdByte := s[2];
    && (
      || (firstByte == 0xE0 && 0xA0 <= secondByte <= 0xBF)
      || (0xE1 <= firstByte <= 0xEC && 0x80 <= secondByte <= 0xBF)
      || (firstByte == 0xED && 0x80 <= secondByte <= 0x9F)
      || (0xEE <= firstByte <= 0xEF && 0x80 <= secondByte <= 0xBF)
    )
    && 0x80 <= thirdByte <= 0xBF
  }

  function method IsWellFormedQuadrupleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 4
    ensures b ==>
      && !IsWellFormedSingleCodeUnitSequence(s[..1])
      && !IsWellFormedDoubleCodeUnitSequence(s[..2])
      && !IsWellFormedTripleCodeUnitSequence(s[..3])
  {
    var firstByte := s[0];
    var secondByte := s[1];
    var thirdByte := s[2];
    var fourthByte := s[3];
    && (
      || (firstByte == 0xF0 && 0x90 <= secondByte <= 0xBF)
      || (0xF1 <= firstByte <= 0xF3 && 0x80 <= secondByte <= 0xBF)
      || (firstByte == 0xF4 && 0x80 <= secondByte <= 0x8F)
    )
    && 0x80 <= thirdByte <= 0xBF
    && 0x80 <= fourthByte <= 0xBF
  }

  function method SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq):
    (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
  {
    // Attaching the subset types explicitly to work around
    // type inference not picking it (unless Option<T> is declared as Option<+T>).
    // BUG(https://github.com/dafny-lang/dafny/issues/2551)
    if |s| >= 1 && IsWellFormedSingleCodeUnitSequence(s[..1]) then 
      var r: MinimalWellFormedCodeUnitSeq := s[..1]; Some(r)
    else if |s| >= 2 && IsWellFormedDoubleCodeUnitSequence(s[..2]) then
      var r: MinimalWellFormedCodeUnitSeq := s[..2]; Some(r)
    else if |s| >= 3 && IsWellFormedTripleCodeUnitSequence(s[..3]) then
      var r: MinimalWellFormedCodeUnitSeq := s[..3]; Some(r)
    else if |s| >= 4 && IsWellFormedQuadrupleCodeUnitSequence(s[..4]) then
      var r: MinimalWellFormedCodeUnitSeq := s[..4]; Some(r)
    else None
  }

  //
  // Encoding and decoding.
  // See Table 3-6. UTF-8 Bit Distribution of the Unicode Standard 14.0.
  //

  function method EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
  {
    if v <= 0x7F then EncodeScalarValueSingleByte(v)
    else if v <= 0x7FF then EncodeScalarValueDoubleByte(v)
    else if v <= 0xFFFF then EncodeScalarValueTripleByte(v)
    else EncodeScalarValueQuadrupleByte(v)
  }

  function method EncodeScalarValueSingleByte(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 0 <= v <= 0x7F
    ensures |m| == 1
    ensures IsWellFormedSingleCodeUnitSequence(m)
  {
    // v = 0000 0000 / 0xxx xxxx
    var x := (v & 0x7F) as bv7;
    // encoded = 0xxx xxxx
    var firstByte := x as CodeUnit;
    [firstByte]
  }

  function method EncodeScalarValueDoubleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 0x80 <= v <= 0x7FF
    ensures |s| == 2
    ensures IsWellFormedDoubleCodeUnitSequence(s)
  {
    // v = 0000 0yyy / yyxx xxxx
    var x := (v & 0x3F) as bv6;
    var y := ((v & 0x7C0) >> 6) as bv5;
    // encoded = 110y yyyy / 10xx xxxx
    var firstByte := 0xC0 | y as CodeUnit;
    var secondByte := 0x80 | x as CodeUnit;
    [firstByte, secondByte]
  }

  function method EncodeScalarValueTripleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 0x800 <= v <= 0xFFFF
    ensures |s| == 3
    ensures IsWellFormedTripleCodeUnitSequence(s)
  {
    // v = zzzz yyyy / yyxx xxxx
    var x := (v & 0x3F) as bv6;
    var y := ((v & 0xFC0) >> 6) as bv6;
    var z := ((v & 0xF000) >> 12) as bv4;
    // encoded = 1110 zzzz / 10yy yyyy / 10xx xxxx
    var firstByte := 0xE0 | z as CodeUnit;
    var secondByte := 0x80 | y as CodeUnit;
    var thirdByte := 0x80 | x as CodeUnit;
    [firstByte, secondByte, thirdByte]
  }

  function method EncodeScalarValueQuadrupleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 0x10000 <= v <= 0x10FFFF
    ensures |s| == 4
    ensures IsWellFormedQuadrupleCodeUnitSequence(s)
  {
    // v = 000u uuuu / zzzz yyyy / yyxx xxxx
    //        1 1122
    assert v <= 0x1FFFFF;
    var x := (v & 0x3F) as bv6;
    var y := ((v & 0xFC0) >> 6) as bv6;
    var z := ((v & 0xF000) >> 12) as bv4;
    var u2 := ((v & 0x30000) >> 16) as bv2;
    var u1 := ((v & 0x1C0000) >> 18) as bv3;

    // encoded = 1111 0uuu / 10uu zzzz / 10yy yyyy / 10xx xxxx
    //                 111     22
    var firstByte := 0xF0 | u1 as CodeUnit;
    var secondByte := 0x80 | ((u2 as CodeUnit) << 4) | z as CodeUnit;
    var thirdByte := 0x80 | y as CodeUnit;
    var fourthByte := 0x80 | x as CodeUnit;
    [firstByte, secondByte, thirdByte, fourthByte]
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
  {
    if |m| == 1 then DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m)
    else if |m| == 2 then DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m)
    else if |m| == 3 then DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m)
    else assert |m| == 4; DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m)
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 1
    ensures 0 <= v <= 0x7F
    ensures EncodeScalarValueSingleByte(v) == m
  {
    var firstByte := m[0];
    var x := firstByte as bv7;
    x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 2
    ensures 0x80 <= v <= 0x7FF
    ensures EncodeScalarValueDoubleByte(v) == m
  {
    var firstByte := m[0];
    var secondByte := m[1];
    var y := (firstByte & 0x1F) as bv24;
    var x := (secondByte & 0x3F) as bv24;
    (y << 6) | x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 3
    ensures 0x800 <= v <= 0xFFFF
    ensures EncodeScalarValueTripleByte(v) == m
  {
    var firstByte := m[0];
    var secondByte := m[1];
    var thirdByte := m[2];
    var z := (firstByte & 0xF) as bv24;
    var y := (secondByte & 0x3F) as bv24;
    var x := (thirdByte & 0x3F) as bv24;
    (z << 12) | (y << 6) | x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 4
    ensures 0x10000 <= v <= 0x10FFFF
    ensures EncodeScalarValueQuadrupleByte(v) == m
  {
    var firstByte := m[0];
    var secondByte := m[1];
    var thirdByte := m[2];
    var fourthByte := m[3];
    var u1 := (firstByte & 0x7) as bv24;
    var u2 := ((secondByte & 0x30) >> 4) as bv24;
    var z := (secondByte & 0xF) as bv24;
    var y := (thirdByte & 0x3F) as bv24;
    var x := (fourthByte & 0x3F) as bv24;
    var v := (u1 << 18) | (u2 << 16) | (z << 12) | (y << 6) | x as Unicode.ScalarValue;
    assert {:split_here} true;
    assert EncodeScalarValueQuadrupleByte(v) == m;
    v
  }
}
