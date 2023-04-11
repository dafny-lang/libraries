// RUN: %verify --unicode-char:true %s

include "UnicodeStrings.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module UnicodeStrings refines AbstractUnicodeStrings {

  import Unicode
  import Utf8EncodingForm
  import Utf16EncodingForm 
  import Seq

  lemma CharIsUnicodeScalarValue(c: char)
    ensures 
      && var asBits := c as bv24;
      && (0 <= asBits < Unicode.HIGH_SURROGATE_MIN || Unicode.LOW_SURROGATE_MAX < asBits <= 0x10FFFF)
  {
    var asBits := c as bv24;
    assert (asBits < Unicode.HIGH_SURROGATE_MIN || asBits > Unicode.HIGH_SURROGATE_MAX);
    assert (asBits < Unicode.LOW_SURROGATE_MIN || asBits > Unicode.LOW_SURROGATE_MAX);
  }

  lemma UnicodeScalarValueIsChar(sv: Unicode.ScalarValue)
    ensures 
      && var asInt := sv as int;
      && (0 <= asInt < 0xD800 || 0xE000 <= asInt < 0x11_0000)
  {
    var asInt := sv as int;
    assert (asInt < 0xD800 || asInt > 0xDFFF);
    assert (asInt < 0xDBFF || asInt > 0xDC00);
  }

  function CharAsUnicodeScalarValue(c: char): Unicode.ScalarValue {
    CharIsUnicodeScalarValue(c);
    c as Unicode.ScalarValue
  }

  function CharFromUnicodeScalarValue(sv: Unicode.ScalarValue): char {
    UnicodeScalarValueIsChar(sv);
    // TODO: Can we avoid the extra cast to int?
    sv as int as char
  }

  function ToUTF8(s: string): Option<seq<uint8>>
    ensures ToUTF8(s).Some?
  {
    var asCodeUnits := Seq.Map(CharAsUnicodeScalarValue, s);
    var asUtf8CodeUnits := Utf8EncodingForm.EncodeScalarSequence(asCodeUnits);
    var asBytes := Seq.Map(cu => cu as uint8, asUtf8CodeUnits);
    Some(asBytes)
  }

  function FromUTF8(bs: seq<uint8>): Option<string> {
    var asCodeUnits := Seq.Map(c => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32 :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asChars := Seq.Map(CharFromUnicodeScalarValue, utf32);
    Some(asChars)
  }
}